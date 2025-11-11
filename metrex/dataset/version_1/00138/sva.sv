// SVA checker for Control. Focused, high-quality assertions and coverage.
module Control_sva (
  input logic        clk, rst,
  input logic [7:0]  in3, in2, in1, in0,
  input logic [3:0]  anodo,
  input logic [7:0]  catodo
);
  default clocking cb @(posedge clk); endclocking

  // Track if we have a valid past sample outside reset
  logic past_valid;
  always @(posedge clk or posedge rst) if (rst) past_valid <= 1'b0; else past_valid <= 1'b1;

  // anodo must always be one of the 4 valid active-low one-hot codes
  assert property (anodo inside {4'b1110,4'b1101,4'b1011,4'b0111});

  // Reset forces 00 MSBs => anodo=1110, catodo=in0 (holds while rst is 1)
  assert property (rst |-> (anodo==4'b1110 && catodo===in0));

  // Correct multiplexing from anodo selection
  assert property ((anodo==4'b1110) |-> (catodo===in0));
  assert property ((anodo==4'b1101) |-> (catodo===in1));
  assert property ((anodo==4'b1011) |-> (catodo===in2));
  assert property ((anodo==4'b0111) |-> (catodo===in3));

  // anodo can only advance in binary order: 1110->1101->1011->0111->1110 (ignoring reset)
  assert property (disable iff (rst)
    past_valid && $changed(anodo) |->
      (($past(anodo)==4'b1110 && anodo==4'b1101) ||
       ($past(anodo)==4'b1101 && anodo==4'b1011) ||
       ($past(anodo)==4'b1011 && anodo==4'b0111) ||
       ($past(anodo)==4'b0111 && anodo==4'b1110))
  );

  // anodo cannot change on two consecutive cycles (MSBs of free-running counter)
  assert property (disable iff (rst) past_valid && $changed(anodo) |-> !$changed(anodo));

  // Coverage: see all four phases in order (allowing arbitrary dwell between changes)
  cover property (disable iff (rst)
    anodo==4'b1110 ##[1:$] anodo==4'b1101 ##[1:$] anodo==4'b1011 ##[1:$] anodo==4'b0111 ##[1:$] anodo==4'b1110
  );

  // Coverage: reset then post-reset expected anodo
  cover property (rst ##1 !rst and anodo==4'b1110);
endmodule

bind Control Control_sva i_Control_sva (.*);