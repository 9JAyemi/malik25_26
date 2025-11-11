// SVA checker for twos_complement_sum
// Binds to DUT and verifies functionality and key corner cases concisely.

module twos_complement_sum_sva (
  input logic [31:0] input_data,
  input logic [15:0] output_sum,
  input logic [15:0] lower_bits_twos_comp,
  input logic [15:0] upper_bits_twos_comp,
  input logic [15:0] sum
);

  function automatic logic [15:0] twos16 (input logic [15:0] x);
    return (~x) + 16'h1;
  endfunction

  function automatic logic [15:0] add16 (input logic [15:0] a, input logic [15:0] b);
    return a + b; // 16-bit add with wrap due to 16-bit return type
  endfunction

  function automatic logic [15:0] expected_out (input logic [31:0] in);
    logic [15:0] l, u, s;
    begin
      l = twos16(in[15:0]);
      u = twos16(in[31:16]);
      s = add16(l,u);
      return (s > 16'h7FFF) ? 16'h7FFF : s;
    end
  endfunction

  // Knownness
  assert property (@(input_data or lower_bits_twos_comp or upper_bits_twos_comp or sum or output_sum)
                   !$isunknown(input_data) |-> !$isunknown({lower_bits_twos_comp, upper_bits_twos_comp, sum, output_sum}))
    else $error("X/Z detected on internal/output when input_data known");

  // Internal computations
  assert property (@(input_data)
                   !$isunknown(input_data[15:0]) |-> (lower_bits_twos_comp == twos16(input_data[15:0])))
    else $error("lower_bits_twos_comp mismatch");
  assert property (@(input_data)
                   !$isunknown(input_data[31:16]) |-> (upper_bits_twos_comp == twos16(input_data[31:16])))
    else $error("upper_bits_twos_comp mismatch");
  assert property (@(lower_bits_twos_comp or upper_bits_twos_comp)
                   !$isunknown({lower_bits_twos_comp,upper_bits_twos_comp}) |-> (sum == add16(lower_bits_twos_comp, upper_bits_twos_comp)))
    else $error("sum mismatch vs lower+upper");

  // Saturation behavior
  assert property (@(sum or output_sum)
                   !$isunknown(sum) && (sum > 16'h7FFF) |-> (output_sum == 16'h7FFF))
    else $error("Saturation high case failed");
  assert property (@(sum or output_sum)
                   !$isunknown(sum) && (sum <= 16'h7FFF) |-> (output_sum == sum))
    else $error("Non-saturation case failed");

  // End-to-end functional spec from inputs to output
  assert property (@(input_data or output_sum)
                   !$isunknown(input_data) |-> (output_sum == expected_out(input_data)))
    else $error("Output does not match functional spec");

  // Coverage: hit both paths and key boundaries
  cover property (@(input_data)
                  add16(twos16(input_data[15:0]), twos16(input_data[31:16])) > 16'h7FFF
                  && output_sum == 16'h7FFF);
  cover property (@(input_data)
                  add16(twos16(input_data[15:0]), twos16(input_data[31:16])) <= 16'h7FFF
                  && output_sum == add16(twos16(input_data[15:0]), twos16(input_data[31:16])));
  cover property (@(sum) sum == 16'h7FFF && output_sum == 16'h7FFF);
  cover property (@(sum) sum == 16'h8000 && output_sum == 16'h7FFF);
  cover property (@(sum) sum == 16'h0000 && output_sum == 16'h0000);
  cover property (@(input_data) input_data[15:0] == 16'h8000);
  cover property (@(input_data) input_data[31:16] == 16'h8000);

endmodule

// Bind to DUT (connects to internals for thorough checking)
bind twos_complement_sum twos_complement_sum_sva u_twos_complement_sum_sva (
  .input_data(input_data),
  .output_sum(output_sum),
  .lower_bits_twos_comp(lower_bits_twos_comp),
  .upper_bits_twos_comp(upper_bits_twos_comp),
  .sum(sum)
);