// SVA for Timer
module Timer_sva(
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  ten,
  input logic [3:0]  one,
  input logic        isFinished
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property ( !$isunknown({rst_n,ten,one,isFinished}) );
  assert property ( one <= 4'd9 );
  assert property ( ten <= 4'd3 );

  // Reset behavior
  assert property ( !rst_n |-> (ten==4'd3 && one==4'd0) );
  assert property ( $rose(rst_n) |=> (ten==4'd2 && one==4'd9) );

  // isFinished correctness and terminal hold
  assert property ( isFinished == (ten==4'd0 && one==4'd0) );
  assert property ( disable iff (!rst_n)
                    isFinished |=> (ten==4'd0 && one==4'd0 && $stable({ten,one,isFinished})) );

  // Next-state rules
  assert property ( disable iff (!rst_n)
                    (!isFinished && (one>4'd0)) |=> (ten==$past(ten) && one==$past(one)-4'd1) );

  assert property ( disable iff (!rst_n)
                    (!isFinished && (one==4'd0)) |=> (ten==$past(ten)-4'd1 && one==4'd9) );

  // Coverage
  cover property ( $rose(rst_n) ##1 (ten==4'd2 && one==4'd9)
                   ##[1:$] (ten==4'd0 && one==4'd0 && isFinished) );

  cover property ( disable iff (!rst_n)
                   (!isFinished && one>4'd0) ##1 (one==$past(one)-4'd1) );

  cover property ( disable iff (!rst_n)
                   (!isFinished && one==4'd0) ##1 (one==4'd9 && ten==$past(ten)-4'd1) );

  cover property ( disable iff (!rst_n) isFinished [*3] );
endmodule

// Bind into DUT
bind Timer Timer_sva u_timer_sva(.clk(clk), .rst_n(rst_n), .ten(ten), .one(one), .isFinished(isFinished));