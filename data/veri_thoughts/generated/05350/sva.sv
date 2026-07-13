module selector_module_sva (
    input logic       clk,
    input logic [1:0] SEL,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] OUT
);

    wire [7:0] sum;
    wire [7:0] diff;
    wire [7:0] prod;
    wire [7:0] quo;

    assign sum  = A + B;
    assign diff = A - B;
    assign prod = A * B;
    assign quo  = A / B;

    // SEL=00 selects the sum result.
    check_select_sum: assert property (
        @(posedge clk) (SEL == 2'b00) |-> (OUT === sum)
    );

    // SEL=01 selects the difference result.
    check_select_diff: assert property (
        @(posedge clk) (SEL == 2'b01) |-> (OUT === diff)
    );

    // SEL=10 selects the product result.
    check_select_prod: assert property (
        @(posedge clk) (SEL == 2'b10) |-> (OUT === prod)
    );

    // SEL=11 selects the quotient result.
    check_select_quo: assert property (
        @(posedge clk) (SEL == 2'b11) |-> (OUT === quo)
    );

    // Stable inputs imply a stable sampled output.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({SEL, A, B}) |-> $stable(OUT)
    );

endmodule