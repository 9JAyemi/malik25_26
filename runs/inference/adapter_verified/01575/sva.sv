module parity_check_sva (
    input logic clk,
    input logic [7:0] data,
    input logic parity_error
);

// parity_error must equal the XOR reduction of data.
    check_parity_equation: assert property (
        @(posedge clk) parity_error == (^data)
    );

// A zero input must drive parity_error low.
    check_zero_input: assert property (
        @(posedge clk) (data == 8'h00) |-> (parity_error == 1'b0)
    );

// An input with even parity must drive parity_error low.
    check_even_parity: assert property (
        @(posedge clk) (^data == 1'b0) |-> (parity_error == 1'b0)
    );

// An input with odd parity must drive parity_error high.
    check_odd_parity: assert property (
        @(posedge clk) (^data == 1'b1) |-> (parity_error == 1'b1)
    );

endmodule
