// SVA checker for axi_traffic_gen_v2_0_7_ex_fifo
module axi_traffic_gen_v2_0_7_ex_fifo_sva #(
  parameter WIDTH        = 10,
  parameter DEPTH        = 8,
  parameter DEPTHBITS    = 3,
  parameter HEADREG      = 1,
  parameter ZERO_INVALID = 0,
  parameter FULL_LEVEL   = 6,
  parameter BLOCK_ACTIVE = 0
)(
  input                   Clk,
  input                   rst_l,
  input  [WIDTH-1:0]      in_data,
  input                   in_push,
  input                   in_pop,
  input  [WIDTH-1:0]      out_data,
  input                   is_full,
  input                   is_notfull,
  input                   is_empty,
  input                   out_valid,
  input  [15:0]           ex_fifo_dbgout
);

  // Simple reference model
  localparam int ADDRW = DEPTHBITS;

  logic [ADDRW-1:0] wr_ptr, rd_ptr;
  logic [ADDRW  :0] depth_m;       // 0..DEPTH
  logic [WIDTH-1:0] mem [0:DEPTH-1];

  // model head (current cycle) and a 1-cycle delayed copy
  logic [WIDTH-1:0] head_cur, head_q;

  // helpers
  function automatic [ADDRW-1:0] inc_ptr(input [ADDRW-1:0] ptr);
    return (ptr == DEPTH-1) ? '0 : (ptr + 1'b1);
  endfunction

  // synchronous reference model
  always_ff @(posedge Clk) begin
    if (!rst_l) begin
      wr_ptr  <= '0;
      rd_ptr  <= '0;
      depth_m <= '0;
      head_q  <= '0;
      head_cur<= '0;
    end else begin
      // compute next pointers
      logic push = in_push;
      logic pop  = in_pop;

      logic [ADDRW-1:0] wr_ptr_n = push ? inc_ptr(wr_ptr) : wr_ptr;
      logic [ADDRW-1:0] rd_ptr_n = pop  ? inc_ptr(rd_ptr) : rd_ptr;

      // write on push
      if (push) mem[wr_ptr] <= in_data;

      // depth (clamped to legal range; illegal use is asserted separately)
      unique case ({push,pop})
        2'b10: depth_m <= (depth_m < DEPTH) ? depth_m + 1 : depth_m;
        2'b01: depth_m <= (depth_m > 0)     ? depth_m - 1 : '0;
        default: depth_m <= depth_m;
      endcase

      // update pointers
      wr_ptr <= wr_ptr_n;
      rd_ptr <= rd_ptr_n;

      // compute head for current cycle after updates; handle push/pop corner
      head_cur <= (pop && (depth_m == 1)) ? in_data : mem[rd_ptr_n];

      // pipeline for HEADREG case
      head_q <= head_cur;
    end
  end

  // Basic protocol safety (no underflow/overflow)
  // Underflow: pop when empty (without concurrent push) is illegal
  assert_no_underflow: assert property (@(posedge Clk) disable iff(!rst_l)
    !( (depth_m == 0) && in_pop && !in_push )
  );

  // Overflow: push when at max depth (without concurrent pop) is illegal
  assert_no_overflow: assert property (@(posedge Clk) disable iff(!rst_l)
    !( (depth_m == DEPTH) && in_push && !in_pop )
  );

  // out_valid equals occupancy!=0 (BLOCK_ACTIVE==0)
  generate if (BLOCK_ACTIVE == 0) begin
    assert_out_valid: assert property (@(posedge Clk) disable iff(!rst_l)
      out_valid == (depth_m != 0)
    );
  end endgenerate

  // is_empty reflects occupancy==0
  assert_is_empty: assert property (@(posedge Clk) disable iff(!rst_l)
    is_empty == (depth_m == 0)
  );

  // is_full / is_notfull reflect FULL_LEVEL (BLOCK_ACTIVE==0)
  generate if (BLOCK_ACTIVE == 0) begin
    assert_is_full: assert property (@(posedge Clk) disable iff(!rst_l)
      is_full == (depth_m >= FULL_LEVEL)
    );
    assert_is_notfull: assert property (@(posedge Clk) disable iff(!rst_l)
      is_notfull == ~ (depth_m >= FULL_LEVEL)
    );
  end endgenerate

  // ex_fifo_dbgout mirrors depth (lower bits) and zero-extends to 16
  assert_dbgout_lower: assert property (@(posedge Clk) disable iff(!rst_l)
    ex_fifo_dbgout[DEPTHBITS:0] == depth_m
  );
  assert_dbgout_upper_zero: assert property (@(posedge Clk) disable iff(!rst_l)
    ex_fifo_dbgout[15:DEPTHBITS+1] == '0
  );

  // Data correctness when valid
  generate
    if (HEADREG == 0) begin
      // direct head
      assert_data_when_valid: assert property (@(posedge Clk) disable iff(!rst_l)
        out_valid |-> (out_data == head_cur)
      );
    end else begin
      // registered head (1-cycle latency)
      assert_data_when_valid_reg: assert property (@(posedge Clk) disable iff(!rst_l)
        out_valid |-> (out_data == head_q)
      );
    end
  endgenerate

  // ZERO_INVALID gating
  generate if (ZERO_INVALID != 0) begin
    assert_zero_when_invalid: assert property (@(posedge Clk) disable iff(!rst_l)
      !out_valid |-> (out_data == '0)
    );
  end endgenerate

  // Outputs not X/Z when out of reset
  assert_no_x_outs: assert property (@(posedge Clk) disable iff(!rst_l)
    !$isunknown({out_valid,is_full,is_notfull,is_empty,out_data})
  );

  // Depth transition checks
  assert_depth_inc: assert property (@(posedge Clk) disable iff(!rst_l)
    (in_push && !in_pop && (depth_m < DEPTH)) |=> (depth_m == $past(depth_m)+1)
  );
  assert_depth_dec: assert property (@(posedge Clk) disable iff(!rst_l)
    (in_pop && !in_push && ($past(depth_m) > 0)) |=> (depth_m == $past(depth_m)-1)
  );
  assert_depth_hold: assert property (@(posedge Clk) disable iff(!rst_l)
    (in_push && in_pop) |=> (depth_m == $past(depth_m))
  );

  // Coverage
  cover_reach_full_level: cover property (@(posedge Clk) disable iff(!rst_l)
    (BLOCK_ACTIVE==0) && (depth_m < FULL_LEVEL)
    ##[1:$] (depth_m >= FULL_LEVEL) ##1 is_full
  );

  cover_empty_to_nonempty: cover property (@(posedge Clk) disable iff(!rst_l)
    (depth_m == 0) && in_push && !in_pop ##1 out_valid
  );

  cover_wrap_wrptr: cover property (@(posedge Clk) disable iff(!rst_l)
    (wr_ptr == DEPTH-1) && in_push ##1 (wr_ptr == '0)
  );

  cover_simul_push_pop: cover property (@(posedge Clk) disable iff(!rst_l)
    (depth_m inside {[1:DEPTH-1]}) && in_push && in_pop
  );

  cover_bypass_case: cover property (@(posedge Clk) disable iff(!rst_l)
    (depth_m == 1) && in_push && in_pop
  );

  generate if (ZERO_INVALID != 0) begin
    cover_zero_invalid: cover property (@(posedge Clk) disable iff(!rst_l)
      !out_valid && (out_data == '0)
    );
  end endgenerate

endmodule

// Bind into DUT
bind axi_traffic_gen_v2_0_7_ex_fifo
  axi_traffic_gen_v2_0_7_ex_fifo_sva #(
    .WIDTH(WIDTH),
    .DEPTH(DEPTH),
    .DEPTHBITS(DEPTHBITS),
    .HEADREG(HEADREG),
    .ZERO_INVALID(ZERO_INVALID),
    .FULL_LEVEL(FULL_LEVEL),
    .BLOCK_ACTIVE(BLOCK_ACTIVE)
  ) u_axi_traffic_gen_v2_0_7_ex_fifo_sva (.*);