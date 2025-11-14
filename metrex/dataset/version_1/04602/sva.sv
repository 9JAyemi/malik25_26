// SVA for abs_difference_sum
// Bindable, concise, and focused on functional correctness and key corner cases

module abs_difference_sum_sva (
  input  logic [15:0] input_a,
  input  logic [15:0] input_b,
  input  logic [15:0] output_sum
);

  function automatic logic [3:0] abs4 (input logic [3:0] a, b);
    abs4 = (a >= b) ? (a - b) : (b - a);
  endfunction

  default disable iff ($isunknown({input_a,input_b}));

  // Correctness: each nibble equals abs difference of corresponding nibble
  genvar g;
  generate
    for (g=0; g<4; g++) begin : G
      localparam int L = g*4;
      localparam int H = L+3;

      property p_nibble_abs_correct;
        @(input_a or input_b)
          ##0 (output_sum[H:L] === abs4(input_a[H:L], input_b[H:L]));
      endproperty
      assert property (p_nibble_abs_correct);

      // Zero when equal
      property p_nibble_zero_when_equal;
        @(input_a or input_b)
          (input_a[H:L] == input_b[H:L]) |-> ##0 (output_sum[H:L] == 4'd0);
      endproperty
      assert property (p_nibble_zero_when_equal);
    end
  endgenerate

  // Whole-bus equivalence (ordering check)
  property p_bus_pack_correct;
    @(input_a or input_b)
      ##0 (output_sum === {abs4(input_a[15:12],input_b[15:12]),
                           abs4(input_a[11:8], input_b[11:8]),
                           abs4(input_a[7:4],  input_b[7:4]),
                           abs4(input_a[3:0],  input_b[3:0])});
  endproperty
  assert property (p_bus_pack_correct);

  // No X/Z on outputs when inputs are known
  property p_no_x_on_known_inputs;
    @(input_a or input_b)
      ##0 !$isunknown(output_sum);
  endproperty
  assert property (p_no_x_on_known_inputs);

  // Minimal but meaningful functional coverage
  // - Any nibble equal, greater, less
  cover property (@(input_a or input_b)
    ((input_a[3:0]==input_b[3:0]) || (input_a[7:4]==input_b[7:4]) ||
     (input_a[11:8]==input_b[11:8]) || (input_a[15:12]==input_b[15:12])));

  cover property (@(input_a or input_b)
    ((input_a[3:0] > input_b[3:0]) || (input_a[7:4] > input_b[7:4]) ||
     (input_a[11:8] > input_b[11:8]) || (input_a[15:12] > input_b[15:12])));

  cover property (@(input_a or input_b)
    ((input_a[3:0] < input_b[3:0]) || (input_a[7:4] < input_b[7:4]) ||
     (input_a[11:8] < input_b[11:8]) || (input_a[15:12] < input_b[15:12])));

  // - Extremes anywhere: 0 vs 15 and 15 vs 0
  cover property (@(input_a or input_b)
    ((input_a[3:0]==0 && input_b[3:0]==15) || (input_a[7:4]==0 && input_b[7:4]==15) ||
     (input_a[11:8]==0 && input_b[11:8]==15) || (input_a[15:12]==0 && input_b[15:12]==15)));

  cover property (@(input_a or input_b)
    ((input_a[3:0]==15 && input_b[3:0]==0) || (input_a[7:4]==15 && input_b[7:4]==0) ||
     (input_a[11:8]==15 && input_b[11:8]==0) || (input_a[15:12]==15 && input_b[15:12]==0)));

  // - Full bus equal -> all-zero output
  cover property (@(input_a or input_b) (input_a == input_b) && (output_sum == 16'h0000));

endmodule

// Bind into the DUT
bind abs_difference_sum abs_difference_sum_sva sva_inst (.*);