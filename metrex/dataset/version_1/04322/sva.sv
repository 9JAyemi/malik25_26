// SVA checker for oh_par2ser. Binds to DUT and uses a small reference model
// to verify behavior concisely and thoroughly.

module oh_par2ser_sva #(parameter int PW = 64,
                         parameter int SW = 1);
  localparam int SF = PW/SW;          // serialization factor
  localparam int CW = $clog2(SF);     // counter width (assumed > 0)

  // DUT ports
  input  logic              clk;
  input  logic              nreset;
  input  logic [PW-1:0]     din;
  output logic [SW-1:0]     dout;
  output logic              access_out;
  input  logic              load;
  input  logic              shift;
  input  logic [7:0]        datasize;
  input  logic              lsbfirst;
  input  logic              fill;
  input  logic              wait_in;
  output logic              wait_out;

  // Reference model
  logic [PW-1:0] ref_shiftreg;
  int unsigned    ref_count;
  logic           ref_busy;
  logic [SW-1:0]  ref_dout;

  // Acceptance condition as seen at the ports (matches start_transfer)
  wire accept = load && !wait_in && !ref_busy;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!nreset);

  // Mirror DUT behavior
  always_ff @(posedge clk or negedge nreset) begin
    if (!nreset) begin
      ref_count    <= '0;
      ref_shiftreg <= '0;
    end else begin
      // counter
      if (accept)              ref_count <= datasize;              // load (lower CW bits used by DUT)
      else if (shift && ref_busy) ref_count <= ref_count - 1;

      // shift register (priority to accept over shift)
      if (accept) begin
        ref_shiftreg <= din;
      end else if (shift && lsbfirst) begin
        ref_shiftreg <= {{SW{fill}}, ref_shiftreg[PW-1:SW]};
      end else if (shift) begin
        ref_shiftreg <= {ref_shiftreg[PW-SW-1:0], {SW{fill}}};
      end
    end
  end

  // Combinational reference outputs
  assign ref_busy = (ref_count != 0);
  assign ref_dout = lsbfirst ? ref_shiftreg[SW-1:0]
                             : ref_shiftreg[PW-1:PW-SW];

  // Core equivalence checks
  a_access_matches_busy:    assert property (access_out == ref_busy);
  a_wait_out_mapping:       assert property (wait_out == (wait_in || access_out));
  a_dout_matches_model:     assert property (dout == ref_dout);

  // Start acceptance only when not blocked
  a_no_accept_when_blocked: assert property (load && (wait_in || access_out) |-> !accept);

  // Datasize should be within legal range when accepted (prevents truncation surprises)
  a_datasize_range:         assert property (accept |-> (datasize <= SF));

  // Busy behavior around acceptance and completion
  a_busy_after_accept:      assert property (accept && (datasize > 0) |=> access_out);
  a_idle_after_zero:        assert property (accept && (datasize == 0) |=> !access_out);
  a_busy_drops_on_last:     assert property ($past(access_out) && $past(shift) && ($past(ref_count) == 1) |=> !access_out);

  // Stability when no actions occur
  a_access_stable_no_act:   assert property (!$past(accept) && !$past(shift) |-> access_out == $past(access_out));

  // X checks on outputs
  a_no_x_outputs:           assert property (!$isunknown({access_out, wait_out, dout}));

  // Directional shift sanity (only when two chunks exist)
  generate
    if (2*SW <= PW) begin : g_dir_checks
      // Next chunk observed on dout after a shift (lsbfirst)
      a_lsb_next_chunk: assert property (shift && lsbfirst |=> dout == $past(ref_shiftreg[2*SW-1:SW]));
      // Next chunk observed on dout after a shift (msbfirst)
      a_msb_next_chunk: assert property (shift && !lsbfirst |=> dout == $past(ref_shiftreg[PW-SW-1 -: SW]));
    end
  endgenerate

  // Coverage
  c_accept_lsb:    cover property (accept && lsbfirst && (datasize > 1));
  c_accept_msb:    cover property (accept && !lsbfirst && (datasize > 1));
  c_zero_len:      cover property (accept && (datasize == 0));
  c_full_len:      if (SF <= 255) cover property (accept && (datasize == SF[7:0]));
  c_fill_use:      cover property (fill && shift && !access_out); // exercising fill while idle
  c_gated_start:   cover property (load && wait_in && !access_out);

endmodule

// Bind the checker to the DUT
bind oh_par2ser oh_par2ser_sva #(.PW(PW), .SW(SW)) oh_par2ser_sva_i (.*);