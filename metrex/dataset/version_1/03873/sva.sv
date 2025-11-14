// SVA for LTZ_CDCF
// Bind-friendly checker that covers reset, buffer timing, FSM transitions, and dout update protocol.

module ltz_cdcf_sva #(
  parameter int WIDTH = 1,
  parameter logic [WIDTH-1:0] INITVAL = {WIDTH{1'b0}}
)(
  input  logic                  clk,
  input  logic                  rst_n,
  input  logic [WIDTH-1:0]      din,
  input  logic [WIDTH-1:0]      dout,
  input  logic [WIDTH-1:0]      buff,
  input  logic [1:0]            state,
  input  logic                  neq,
  input  logic                  eq
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // During reset, registers are INITVAL / state==0
  // Override default disable to check while in reset
  ap_reset_vals: assert property (@cb disable iff (1'b0)
    !rst_n |-> (buff==INITVAL && dout==INITVAL && state==2'd0)
  );

  // No X/Z on key regs when out of reset
  ap_no_x_regs: assert property (@cb !$isunknown({buff,dout,state}));

  // buff is a 1-cycle delayed copy of din
  ap_buff_delay: assert property (@cb 1 |=> buff == $past(din));

  // eq/neq combinational sanity
  ap_neq_def: assert property (@cb neq == (buff != dout));
  ap_eq_is_stable_din: assert property (@cb 1 |=> eq == (din == $past(din)));

  // FSM next-state checks
  ap_s0: assert property (@cb (state==2'd0) |=> state == ($past(neq) ? 2'd1 : 2'd0));
  ap_s1: assert property (@cb (state==2'd1) |=> state == ($past(eq)  ? 2'd2 : 2'd1));
  ap_s2: assert property (@cb (state==2'd2) |=> state == ($past(eq)  ? 2'd3 : 2'd1));
  ap_s3: assert property (@cb (state==2'd3) |=> state == 2'd0);

  // dout update protocol: only written one cycle after state==3, else holds
  ap_dout_on_3:         assert property (@cb (state==2'd3) |=> dout == $past(buff));
  ap_dout_hold_other:   assert property (@cb (state!=2'd3) |=> dout == $past(dout));
  ap_state3_implies_neq:assert property (@cb (state==2'd3) |-> (buff != dout));

  // End-to-end: pending change + two consecutive eq -> update on the next cycle
  ap_update_after_two_eq: assert property (@cb
    (state==2'd0 && (buff!=dout)) ##1 eq ##1 eq |=> (dout == $past(buff))
  );

  // Coverage
  cv_full_path:  cover property (@cb (state==2'd0 && (buff!=dout)) ##1 eq ##1 eq ##1 (dout==$past(buff)));
  cv_fallback:   cover property (@cb (state==2'd2 && !eq) |=> state==2'd1);
  cv_hold_in_s0: cover property (@cb (state==2'd0 && !(buff!=dout)) |=> state==2'd0);
  cv_update_evt: cover property (@cb (state==2'd3) ##1 $changed(dout));

endmodule

// Example bind (place in a separate file or a testbench package):
// bind LTZ_CDCF ltz_cdcf_sva #(.WIDTH(WIDTH), .INITVAL(INITVAL))
//   LTZ_CDCF_SVA_I ( .clk(clk), .rst_n(rst_n),
//     .din(din), .dout(dout), .buff(buff), .state(state), .neq(neq), .eq(eq) );