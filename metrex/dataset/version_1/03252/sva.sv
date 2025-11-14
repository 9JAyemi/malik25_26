// SVA checker for binary_splitter_and_full_adder
module binary_splitter_and_full_adder_sva (
  input  logic [2:0] in_vec,
  input  logic [2:0] out_vec,
  input  logic       o2, o1, o0,
  input  logic       a, b, cin,
  input  logic       cout, sum,
  input  logic [4:0] final_output
);

  logic vec_known  = !$isunknown(in_vec);
  logic abc_known  = !$isunknown({a,b,cin});
  logic all_known  = vec_known && abc_known;

  // Combinational assertions (sampled with #0 to avoid NBA races)
  always_comb begin
    if (all_known) begin
      // Splitter correctness
      assert #0 (out_vec == in_vec) else $error("out_vec != in_vec");
      assert #0 ({o2,o1,o0} == in_vec) else $error("{o2,o1,o0} != in_vec");

      // Full adder correctness (sum+carry as 2-bit addition)
      assert #0 ({cout, sum} == a + b + cin) else $error("{cout,sum} != a+b+cin");

      // Functional final_output formatting
      assert #0 (final_output[4:3] == {2{in_vec[2] & in_vec[1]}})
        else $error("final_output[4:3] != replicated AND(o2,o1)");
      assert #0 (final_output[2:1] == {2{in_vec[2] | in_vec[1]}})
        else $error("final_output[2:1] != replicated OR(o2,o1)");
      assert #0 (final_output[0] == sum)
        else $error("final_output[0] != sum");
      // Replication consistency
      assert #0 (final_output[4] == final_output[3]) else $error("final_output[4]!=[3]");
      assert #0 (final_output[2] == final_output[1]) else $error("final_output[2]!=[1]");

      // No X/Z on outputs when inputs known
      assert #0 (!$isunknown({out_vec,o2,o1,o0,cout,sum,final_output}))
        else $error("Outputs contain X/Z while inputs are known");
    end
  end

  // SVA functional coverage
  // Cover all in_vec values
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd0);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd1);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd2);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd3);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd4);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd5);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd6);
  cover property (@(posedge in_vec[0] or negedge in_vec[0]
                   or posedge in_vec[1] or negedge in_vec[1]
                   or posedge in_vec[2] or negedge in_vec[2])
                   vec_known && in_vec == 3'd7);

  // Cover all full-adder input combinations
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b000);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b001);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b010);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b011);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b100);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b101);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b110);
  cover property (@(posedge a or negedge a or posedge b or negedge b
                   or posedge cin or negedge cin)
                   abc_known && {a,b,cin} == 3'b111);

endmodule

// Bind the checker to the DUT
bind binary_splitter_and_full_adder binary_splitter_and_full_adder_sva u_binary_splitter_and_full_adder_sva (.*);