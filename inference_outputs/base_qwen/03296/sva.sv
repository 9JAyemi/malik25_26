module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] shift_amt,
    input logic mode,
    output logic [3:0] out
);

    // Instantiate the compare_signed_mag module
    wire equal, signed_larger, signed_smaller;
    wire [3:0] larger_num, smaller_num;
    compare_signed_mag cmp (
        .A(A),
        .B(B),
        .equal(equal),
        .signed_larger(signed_larger),
        .signed_smaller(signed_smaller),
        .larger_num(larger_num),
        .smaller_num(smaller_num)
    );

    // Instantiate the shift_right module
    wire [3:0] shifted_num;
    shift_right shift (
        .in(larger_num),
        .shift_amt(shift_amt),
        .mode(mode),
        .out(shifted_num)
    );

    // Assign the output based on the comparison results
    always @(*) begin
        if (equal) begin
            out = 0;
        end else if (signed_larger) begin
            out = shifted_num;
        end else begin
            out = smaller_num;
        end
    end

    // Assertions
    // Check if equal is set correctly
    equal_check: assert property (
        @(posedge clk) disable iff (!rst_n) equal |-> (A == B)
    ) else $error("Equal is not set correctly");

    // Check if signed_larger is set correctly
    signed_larger_check: assert property (
        @(posedge clk) disable iff (!rst_n) signed_larger |-> ($signed(A) > $signed(B))
    ) else $error("Signed larger is not set correctly");

    // Check if signed_smaller is set correctly
    signed_smaller_check: assert property (
        @(posedge clk) disable iff (!rst_n) signed_smaller |-> ($signed(A) < $signed(B))
    ) else $error("Signed smaller is not set correctly");

    // Check if larger_num is set correctly
    larger_num_check: assert property (
        @(posedge clk) disable iff (!rst_n) larger_num |-> (signed_larger ? A : B)
    ) else $error("Larger number is not set correctly");

    // Check if smaller_num is set correctly
    smaller_num_check: assert property (
        @(posedge clk) disable iff (!rst_n) smaller_num |-> (signed_smaller ? A : B)
    ) else $error("Smaller number is not set correctly");

    // Check if out is set correctly when equal
    out_equal_check: assert property (
        @(posedge clk) disable iff (!rst_n) (equal) |-> (out == 0)
    ) else $error("Output is not set correctly when equal");

    // Check if out is set correctly when signed_larger
    out_signed_larger_check: assert property (
        @(posedge clk) disable iff (!rst_n) (signed_larger) |-> (out == shifted_num)
    ) else $error("Output is not set correctly when signed larger");

    // Check if out is set correctly when signed_smaller
    out_signed_smaller_check: assert property (
        @(posedge clk) disable iff (!rst_n) (signed_smaller) |-> (out == smaller_num)
    ) else $error("Output is not set correctly when signed smaller");

endmodule