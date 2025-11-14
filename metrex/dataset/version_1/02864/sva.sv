// SVA for mealy_fsm – concise, high-quality checks and coverage
module mealy_fsm_sva #(
  parameter A = 3'b000,
  parameter B = 3'b001,
  parameter C = 3'b010,
  parameter D = 3'b011,
  parameter E = 3'b100
) (
  input  logic       clk,
  input  logic       reset,
  input  logic       in1,
  input  logic       in2,
  input  logic       out,
  input  logic [2:0] state
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |-> (state==A && out==0));

  // State legality (E and other encodings are illegal)
  assert property (!reset |-> (state inside {A,B,C,D}));

  // Output is Mealy function of inputs
  assert property (disable iff (reset) out == (in1 && !in2));

  // Next-state relation for normal cycles (use previous state, current inputs)
  assert property (disable iff (reset)
    $past(!reset) |-> state ==
      ((in1 && !in2) ? C :
       (in1 &&  in2) ? D :
       ((!in1 && in2) ? (($past(state)==A) ? A : B) :
                        (($past(state)==A) ? B : A)))
  );

  // First cycle after reset deasserts (previous state is A)
  assert property ($rose(!reset) |-> state ==
      ((in1 && !in2) ? C :
       (in1 &&  in2) ? D :
       ((!in1 && in2) ? A : B))
  );

  // No X on key state/output registers
  assert property (!$isunknown(state) && !$isunknown(out));

  // Functional coverage
  cover property (!reset && out==1);
  cover property (!reset && state==A);
  cover property (!reset && state==B);
  cover property (!reset && state==C);
  cover property (!reset && state==D);
  cover property (!reset && in1==0 && in2==0);
  cover property (!reset && in1==0 && in2==1);
  cover property (!reset && in1==1 && in2==0);
  cover property (!reset && in1==1 && in2==1);

  // Key transition coverage
  cover property (disable iff (reset) $past(state)==A && in1==0 && in2==0 && state==B);
  cover property (disable iff (reset) $past(state)!=A && in1==0 && in2==0 && state==A);
  cover property (disable iff (reset) in1==1 && in2==0 && state==C);
  cover property (disable iff (reset) in1==1 && in2==1 && state==D);

endmodule

bind mealy_fsm mealy_fsm_sva #(.A(A),.B(B),.C(C),.D(D),.E(E)) u_mealy_fsm_sva (.*);