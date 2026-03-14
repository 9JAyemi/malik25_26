module multi_io_module_sva (
  input [3:0] input_a,
  input [3:0] input_b,
  input input_c,
  input input_d,
  input input_e,
  input clk,
  input [3:0] output_a,
  input [3:0] output_b,
  input output_c,
  input output_d,
  input output_e
);

  // output_b must pass through input_b
  check_output_b_passthrough: assert property (
    @(posedge clk) output_b == input_b
  );

  // output_c selects inverted input based on input_e
  check_output_c_inversion_mux: assert property (
    @(posedge clk) output_c == (input_e ? ~input_c : ~input_d)
  );

  // output_d reflects (input_a >= input_b)
  check_output_d_ge_relation: assert property (
    @(posedge clk) output_d == (input_a >= input_b)
  );

  // output_e reflects (input_a < input_b)
  check_output_e_lt_relation: assert property (
    @(posedge clk) output_e == (input_a < input_b)
  );

  // output_d and output_e are complements
  check_compare_outputs_complement: assert property (
    @(posedge clk) output_d == !output_e
  );

  // output_a matches the full specified function
  check_output_a_function_full: assert property (
    @(posedge clk)
      output_a == (
        (input_c ^ input_d)
          ? ((input_a >= input_b) ? (input_a - input_b) : (input_a + input_b))
          : ((input_c & input_d) ? (input_a & input_b) : (input_a | input_b))
      )
  );

  // If input_c^input_d and input_a>=input_b, output_a == input_a - input_b
  check_output_a_xor_ge_sub: assert property (
    @(posedge clk) ((input_c ^ input_d) && (input_a >= input_b)) |-> (output_a == (input_a - input_b))
  );

  // If input_c^input_d and input_a<input_b, output_a == input_a + input_b
  check_output_a_xor_lt_add: assert property (
    @(posedge clk) ((input_c ^ input_d) && (input_a < input_b)) |-> (output_a == (input_a + input_b))
  );

  // If input_c==1 and input_d==1, output_a == input_a & input_b
  check_output_a_and_branch: assert property (
    @(posedge clk) ((!(input_c ^ input_d)) && (input_c & input_d)) |-> (output_a == (input_a & input_b))
  );

  // If input_c==0 and input_d==0, output_a == input_a | input_b
  check_output_a_or_branch: assert property (
    @(posedge clk) ((!(input_c ^ input_d)) && !(input_c & input_d)) |-> (output_a == (input_a | input_b))
  );

endmodule