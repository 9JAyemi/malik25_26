// SVA bind module for mux2_1
module mux2_1_sva (
  input  logic [7:0] input1,
  input  logic [7:0] input2,
  input  logic       select,
  input  logic [7:0] selected_out
);

  // Core functional correctness on any relevant change
  assert property (@(input1 or input2 or select)
                   ##0 selected_out == (select ? input2 : input1))
    else $error("mux2_1 functional mismatch");

  // Select must be 0/1 (no X/Z)
  assert property (@(input1 or input2 or select) !$isunknown(select))
    else $error("mux2_1 select is X/Z");

  // If both data inputs are known, output must be known
  assert property (@(input1 or input2 or select)
                   (!$isunknown(input1) && !$isunknown(input2)) |-> !$isunknown(selected_out))
    else $error("mux2_1 output X/Z with known inputs");

  // Immediate correctness on select edges
  assert property (@(posedge select) ##0 selected_out == input2)
    else $error("mux2_1 failed on select=1 edge");
  assert property (@(negedge select) ##0 selected_out == input1)
    else $error("mux2_1 failed on select=0 edge");

  // Minimal functional coverage
  cover property (@(input1 or input2 or select) (select==0 && selected_out==input1));
  cover property (@(input1 or input2 or select) (select==1 && selected_out==input2));
  cover property (@(posedge select));    // exercised path to input2
  cover property (@(negedge select));    // exercised path to input1
  cover property (@(posedge select) (input1==input2)); // select toggle with equal inputs

endmodule

// Bind into all instances of mux2_1
bind mux2_1 mux2_1_sva sva_mux2_1 (.*);