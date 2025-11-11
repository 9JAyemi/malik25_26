// SVA bind for counter. Focused, concise checks and coverage.
module counter_sva #(parameter int M = 0)
  (input logic clk, rst, cnt,
   input logic [31:0] q,
   input logic ov);

  default clocking cb @(posedge clk); endclocking

  // 32-bit cast of M and (M-1)
  localparam int unsigned MU = M;
  localparam logic [31:0] M32 = MU[31:0];
  localparam logic [31:0] M1  = M32 - 32'd1;

  // Synchronous clear on rst or ov
  ap_rst_clear: assert property ( (rst || ov) |=> (q == 32'd0 && ov == 1'b0) );

  // Hold when no counting and no control
  ap_hold: assert property ( (!rst && !ov && !cnt) |=> (q == $past(q) && ov == $past(ov)) );

  // Increment by exactly 1 when counting
  ap_inc: assert property ( (!rst && !ov && cnt) |=> (q == $past(q) + 32'd1) );

  // Overflow generation exactly at wrap (q == M-1) while counting
  ap_ov_gen: assert property ( (!rst && !ov && cnt && q == M1) |=> (ov && q == $past(q) + 32'd1) );

  // Overflow must only occur due to prior wrap+cnt (no spurious ov)
  ap_ov_src: assert property ( ov |-> $past(!rst && !ov && cnt && q == M1) );

  // Overflow is a single-cycle pulse and auto-clears next cycle
  ap_ov_one: assert property ( ov |=> !ov );

  // Any q change (outside control) must be +1 and only when cnt
  ap_q_change_requires_cnt: assert property (
    (!rst && !ov && (q != $past(q))) |-> (cnt && q == $past(q) + 32'd1)
  );

  // Coverage
  cp_reset: cover property ( rst ##1 (q == 32'd0 && ov == 1'b0) );
  cp_inc:   cover property ( (!rst && !ov && cnt && q != M1) |=> (q == $past(q) + 32'd1) );
  cp_wrap:  cover property ( (!rst && !ov && cnt && q == M1)
                             |=> (ov && q == $past(q) + 32'd1) ##1 (!ov && q == 32'd0) );
  cp_hold:  cover property ( (!rst && !ov && !cnt) |=> (q == $past(q)) );

  // Edge-case coverage for M == 0 (wrap at 0xFFFF_FFFF)
  generate if (M == 0) begin
    cp_m0_wrap: cover property ( (!rst && !ov && cnt && q == 32'hFFFF_FFFF) |=> ov );
  end endgenerate
endmodule

bind counter counter_sva #(.M(M)) counter_sva_i (.*);