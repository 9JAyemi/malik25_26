module top_module_sva (
    input  [31:0] a,
    input  [31:0] b,
    input         select,
    output [31:0] sum
); 

wire [31:0] adder_out;
wire  mux_out;

adder adder_inst (
    .a(a),
    .b(b),
    .sum(adder_out)
);

mux mux_inst (
    .a(a),
    .b(b),
    .c(select),
    .w(mux_out)
);

assign sum = (select == 1'b1) ? adder_out : {31'b0, mux_out};

    ///// Adder logic /////
    // Adder should correctly compute the sum of a and b.
    adder_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (adder_out == a + b)
    );

    ///// Mux logic /////
    // Mux should correctly select between a and b based on the select signal.
    mux_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (mux_out == (select == 1'b1) ? b : a)
    );

    ///// Sum logic /////
    // Sum should correctly select between the adder output and the upper bit of the mux output.
    sum_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (sum == (select == 1'b1) ? adder_out : {31'b0, mux_out})
    );

    ///// Reset behavior /////
    // At reset, sum should be zero.
    reset_sum: assert property (
        @(posedge clk) !reset_n |-> (sum == 32'b0)
    );

endmodule