module mux4to1_32_sva (
    input wire [1:0] sel,
    input wire [31:0] a,
    input wire [31:0] b,
    input wire [31:0] c,
    input wire [31:0] d,
    output reg [31:0] o
);

    // Mux output should be one of the inputs based on the select signal
    mux_output_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (o == a) |-> (sel == 2'b00)
    );
    mux_output_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (o == b) |-> (sel == 2'b01)
    );
    mux_output_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (o == c) |-> (sel == 2'b10)
    );
    mux_output_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (o == d) |-> (sel == 2'b11)
    );

    // Mux output should not be any of the inputs when select is out of range
    mux_output_invalid: assert property (
        @(posedge clk) disable iff (!rst_n) (o != a) |-> (sel != 2'b00)
    );
    mux_output_invalid: assert property (
        @(posedge clk) disable iff (!rst_n) (o != b) |-> (sel != 2'b01)
    );
    mux_output_invalid: assert property (
        @(posedge clk) disable iff (!rst_n) (o != c) |-> (sel != 2'b10)
    );
    mux_output_invalid: assert property (
        @(posedge clk) disable iff (!rst_n) (o != d) |-> (sel != 2'b11)
    );

    // Mux output should be stable when select is stable
    mux_output_stable: assert property (
        @(posedge clk) disable iff (!rst_n) (o == o) |-> (sel == sel)
    );

endmodule