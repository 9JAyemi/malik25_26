module calculator_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [2:0] op,
    input logic [15:0] out
);
    ///// Reset behavior /////
    // On reset, out must be cleared to 0.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 16'h0000)
    );

    ///// Operation decoding /////
    // When op==000 (ADD) and not in reset, out equals A + B.
    check_add_output: assert property (
        @(posedge clk) disable iff (reset) (op == 3'b000) |-> (out == (A + B))
    );
    // When op==001 (SUB) and not in reset, out equals A - B.
    check_sub_output: assert property (
        @(posedge clk) disable iff (reset) (op == 3'b001) |-> (out == (A - B))
    );
    // When op==010 (MUL) and not in reset, out equals A * B.
    check_mul_output: assert property (
        @(posedge clk) disable iff (reset) (op == 3'b010) |-> (out == (A * B))
    );
    // When op==011 (DIV) with B!=0 and not in reset, out equals A / B.
    check_div_output_when_B_nonzero: assert property (
        @(posedge clk) disable iff (reset) (op == 3'b011 && B != 8'h00) |-> (out == (A / B))
    );
    // For any undefined op (100,101,110,111) and not in reset, out must be 0.
    check_default_zero: assert property (
        @(posedge clk) disable iff (reset) (op inside {3'b100,3'b101,3'b110,3'b111}) |-> (out == 16'h0000)
    );

    ///// Functional consistency /////
    // If inputs (A,B,op) are stable and not dividing by zero, out remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset)
            $stable({A,B,op}) && !(op == 3'b011 && B == 8'h00) |-> $stable(out)
    );
endmodule