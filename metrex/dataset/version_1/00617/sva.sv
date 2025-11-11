// SVA for fg_packet_gen
// Bind this module to the DUT instance:
// bind fg_packet_gen fg_packet_gen_sva #(.DEST_WIDTH(DEST_WIDTH), .DATA_WIDTH(DATA_WIDTH), .KEEP_WIDTH(KEEP_WIDTH)) fg_packet_gen_sva_i ();

module fg_packet_gen_sva #(parameter DEST_WIDTH=8, parameter DATA_WIDTH=64, parameter KEEP_WIDTH=(DATA_WIDTH/8)) ();
  // Access DUT signals hierarchically in bound scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  function automatic bit keep_is_contiguous_from_lsb (logic [KEEP_WIDTH-1:0] k);
    return (k != '0) && ((k & (k + 1'b1)) == '0);
  endfunction

  // Environment assumptions
  assume property (input_bd_valid && !input_bd_ready |-> $stable(input_bd_dest) && $stable(input_bd_burst_len));
  assume property (payload_mtu > 0);
  assume property (input_bd_valid |-> input_bd_burst_len > 0);

  // BD handshake only when previously idle
  assert property (input_bd_valid && input_bd_ready |-> $past(!busy));

  // Header channel protocol
  assert property (output_hdr_valid && !output_hdr_ready |-> $stable(output_hdr_valid) && $stable(output_hdr_dest) && $stable(output_hdr_len));
  assert property (output_hdr_valid && output_hdr_ready |=> !output_hdr_valid);
  assert property (output_hdr_valid && output_hdr_ready |-> (output_hdr_len inside {[16'd1:payload_mtu]}));

  // Track BD fields and remaining length
  logic [DEST_WIDTH-1:0] exp_hdr_dest;
  logic [31:0]           rem_len;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      exp_hdr_dest <= '0;
      rem_len      <= 32'd0;
    end else begin
      if (input_bd_valid && input_bd_ready) begin
        exp_hdr_dest <= input_bd_dest;
        rem_len      <= input_bd_burst_len;
      end else if (output_hdr_valid && output_hdr_ready) begin
        rem_len <= (rem_len > payload_mtu) ? (rem_len - payload_mtu) : 32'd0;
      end
    end
  end
  assert property (output_hdr_valid && output_hdr_ready |-> output_hdr_dest == exp_hdr_dest);
  assert property (output_hdr_valid && output_hdr_ready |-> output_hdr_len == ((rem_len > payload_mtu) ? payload_mtu : rem_len));

  // One header per frame; header precedes payload
  logic in_frame;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) in_frame <= 1'b0;
    else begin
      if (input_bd_valid && input_bd_ready) in_frame <= 1'b0;
      if (output_hdr_valid && output_hdr_ready) in_frame <= 1'b1;
      if (output_payload_tvalid && output_payload_tready && output_payload_tlast) in_frame <= 1'b0;
    end
  end
  assert property (in_frame |-> !(output_hdr_valid && output_hdr_ready));
  assert property ((output_payload_tvalid && output_payload_tready) |-> in_frame);

  // Payload channel protocol
  assert property (output_payload_tvalid && !output_payload_tready |-> $stable(output_payload_tdata) && $stable(output_payload_tkeep) && $stable(output_payload_tlast) && $stable(output_payload_tuser));
  assert property (output_payload_tvalid |-> (output_payload_tuser == 1'b0));
  assert property (output_payload_tvalid && output_payload_tready && !output_payload_tlast |-> output_payload_tkeep == {KEEP_WIDTH{1'b1}});
  assert property (output_payload_tvalid && output_payload_tready && output_payload_tlast |-> keep_is_contiguous_from_lsb(output_payload_tkeep));

  // For each header, total payload bytes must equal header length
  property p_hdr_payload_bytecount;
    int unsigned sum;
    (output_hdr_valid && output_hdr_ready, sum = 0)
      |->
      (##[0:$] (output_payload_tvalid && output_payload_tready, sum += $countones(output_payload_tkeep))
        [*0:$]
       ##1 (output_payload_tvalid && output_payload_tready && output_payload_tlast && (sum + $countones(output_payload_tkeep) == output_hdr_len)));
  endproperty
  assert property (p_hdr_payload_bytecount);

  // Optional internal check (skid/early-ready)
`ifdef ASSERT_INTERNALS
  assert property ((!temp_payload_tvalid_reg && !output_payload_tvalid_reg) |-> output_payload_tready_int_early);
`endif

  // Coverage
  cover property (input_bd_valid && input_bd_ready);
  cover property (output_hdr_valid && output_hdr_ready);
  cover property (output_payload_tvalid && output_payload_tready && output_payload_tlast);

  // Multiple frames for one BD (burst_len > mtu)
  cover property (input_bd_valid && input_bd_ready && (input_bd_burst_len > payload_mtu)
                  ##[1:$] (output_hdr_valid && output_hdr_ready && output_hdr_len == payload_mtu)
                  ##[1:$] (output_hdr_valid && output_hdr_ready && output_hdr_len <= payload_mtu));

  // Multi-beat frame with partial last
  cover property ((output_hdr_valid && output_hdr_ready && output_hdr_len > KEEP_WIDTH && (output_hdr_len % KEEP_WIDTH) != 0)
                  ##[0:$] (output_payload_tvalid && output_payload_tready && !output_payload_tlast)
                  ##[1:$] (output_payload_tvalid && output_payload_tready && output_payload_tlast && keep_is_contiguous_from_lsb(output_payload_tkeep) && output_payload_tkeep != {KEEP_WIDTH{1'b1}}));

  // Aligned last beat (keep all ones)
  cover property ((output_hdr_valid && output_hdr_ready && (output_hdr_len % KEEP_WIDTH) == 0)
                  ##[0:$] (output_payload_tvalid && output_payload_tready && output_payload_tlast && output_payload_tkeep == {KEEP_WIDTH{1'b1}}));

  // Backpressure scenarios
  cover property (output_payload_tvalid && !output_payload_tready ##1 output_payload_tvalid && !output_payload_tready ##1 output_payload_tvalid && output_payload_tready);
  cover property (output_hdr_valid && !output_hdr_ready ##1 output_hdr_valid && !output_hdr_ready ##1 output_hdr_valid && output_hdr_ready);
endmodule