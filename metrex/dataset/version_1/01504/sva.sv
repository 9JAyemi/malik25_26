// SVA for sum_threshold: concise, high-quality checks and coverage
module sum_threshold_sva(input logic [15:0] in, input logic [3:0] out);

  function automatic [6:0] sum4(input logic [15:0] v);
    sum4 = v[3:0] + v[7:4] + v[11:8] + v[15:12];
  endfunction

  // Functional correctness on same-delta after input change
  a_func: assert property (@(in) !$isunknown(in) |-> ##0 (out == {4{sum4(in) >= 8}}));

  // Redundancy check: all out bits must be identical
  a_bits_equal: assert property (@(in) 1 |-> ##0 (out === {4{out[0]}}));

  // No X/Z on outputs when inputs are known
  a_no_x_out: assert property (@(in) !$isunknown(in) |-> ##0 !$isunknown(out));

  // Coverage: below/at/above threshold and extremes
  c_below: cover property (@(in) (sum4(in) < 8)  ##0 (out == 4'b0000));
  c_at:    cover property (@(in) (sum4(in) == 8) ##0 (out == 4'b1111));
  c_above: cover property (@(in) (sum4(in) > 8)  ##0 (out == 4'b1111));
  c_zero:  cover property (@(in) (sum4(in) == 0));
  c_max:   cover property (@(in) (sum4(in) == 60));

endmodule

bind sum_threshold sum_threshold_sva u_sum_threshold_sva (.in(in), .out(out));