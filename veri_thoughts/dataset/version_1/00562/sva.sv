module mux4x1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] S,
    input logic Y
);

    // Y must match the RTL mux expression on every sampled cycle.
    check_mux_function: assert property (
        @(posedge clk)
        Y === ((S == 2'b00) ? A :
               (S == 2'b01) ? B :
               (S == 2'b10) ? C :
                              D)
    );

    // Select 00 routes A to Y.
    check_select_a: assert property (
        @(posedge clk)
        (S === 2'b00) |-> (Y === A)
    );

    // Select 01 routes B to Y.
    check_select_b: assert property (
        @(posedge clk)
        (S === 2'b01) |-> (Y === B)
    );

    // Select 10 routes C to Y.
    check_select_c: assert property (
        @(posedge clk)
        (S === 2'b10) |-> (Y === C)
    );

    // Select 11 routes D to Y.
    check_select_d: assert property (
        @(posedge clk)
        (S === 2'b11) |-> (Y === D)
    );

endmodule