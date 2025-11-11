// SVA for Calculator_Full_Adder
module Calculator_Full_Adder_sva #(parameter WIDTH=4)
(
  input  logic [WIDTH-1:0] A,
  input  logic [WIDTH-1:0] B,
  input  logic             CIN,
  input  logic [WIDTH-1:0] RES,
  input  logic             COUT
);

  localparam logic [WIDTH-1:0] ALL_ONES = {WIDTH{1'b1}};
  localparam logic [WIDTH-1:0] ONE      = {{(WIDTH-1){1'b0}},1'b1};
  localparam logic [WIDTH-1:0] MAX_POS  = {1'b0, {(WIDTH-1){1'b1}}};
  localparam logic [WIDTH-1:0] MIN_NEG  = {1'b1, {(WIDTH-1){1'b0}}};

  // Functional correctness (combinational)
  assert property (@(A or B or CIN)
    {COUT,RES} == ($signed({A[WIDTH-1],A}) + $signed({B[WIDTH-1],B}) + CIN)
  );

  // Lower WIDTH bits must match plain unsigned sum
  assert property (@(A or B or CIN)
    RES == (A + B + CIN)[WIDTH-1:0]
  );

  // No X/Z on outputs when inputs are known
  assert property (@(A or B or CIN)
    !$isunknown({A,B,CIN}) |-> !$isunknown({RES,COUT})
  );

  // Coverage: exercise carry, overflow, and boundary cases
  cover property (@(A or B or CIN) CIN==0);
  cover property (@(A or B or CIN) CIN==1);
  cover property (@(A or B or CIN) COUT==1);                   // carry/overflow bit set
  cover property (@(A or B or CIN) !(COUT ^ RES[WIDTH-1]));    // no signed overflow
  cover property (@(A or B or CIN)  (COUT ^ RES[WIDTH-1]));    // signed overflow (either direction)
  cover property (@(A or B or CIN) (A[WIDTH-1]==0 && B[WIDTH-1]==0 && (COUT ^ RES[WIDTH-1]))); // + overflow
  cover property (@(A or B or CIN) (A[WIDTH-1]==1 && B[WIDTH-1]==1 && (COUT ^ RES[WIDTH-1]))); // - overflow
  cover property (@(A or B or CIN) (A==MAX_POS && B==ONE  && CIN==0)); // boundary: max_pos + 1
  cover property (@(A or B or CIN) (A==MIN_NEG && B==ALL_ONES && CIN==0)); // boundary: min_neg + (-1)
  cover property (@(A or B or CIN) (A==ALL_ONES && B==ALL_ONES && CIN==1)); // heavy carry
  cover property (@(A or B or CIN) RES=={WIDTH{1'b0}});        // zero result case

endmodule

// Bind to DUT
bind Calculator_Full_Adder
  Calculator_Full_Adder_sva #(.WIDTH(WIDTH))
  Calculator_Full_Adder_sva_i (.*);