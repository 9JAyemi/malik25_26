module RegisterAdd_1_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [0:0] D,
    input logic [0:0] Q
);

    // clk is the sampling clock; rst is active high.
    // Mixed logic: Q is sequential, and next-state is combinational.

    // When load is high and D is 0, the next Q is 0.
    check_load_zero_captures_zero: assert property (
        @(posedge clk) disable iff (rst)
        (load && (D == 1'b0)) |=> (Q == 1'b0)
    );

    // When load is high and D is 1, the next Q is 1.
    check_load_one_captures_one: assert property (
        @(posedge clk) disable iff (rst)
        (load && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // When load is low, D is 0, and Q is 0, Q stays 0.
    check_add_zero_holds_zero: assert property (
        @(posedge clk) disable iff (rst)
        (!load && (D == 1'b0) && (Q == 1'b0)) |=> (Q == 1'b0)
    );

    // When load is low, D is 0, and Q is 1, Q stays 1.
    check_add_zero_holds_one: assert property (
        @(posedge clk) disable iff (rst)
        (!load && (D == 1'b0) && (Q == 1'b1)) |=> (Q == 1'b1)
    );

    // When load is low, D is 1, and Q is 0, Q becomes 1.
    check_add_one_sets_one: assert property (
        @(posedge clk) disable iff (rst)
        (!load && (D == 1'b1) && (Q == 1'b0)) |=> (Q == 1'b1)
    );

    // When load is low, D is 1, and Q is 1, Q becomes 0.
    check_add_one_clears_zero: assert property (
        @(posedge clk) disable iff (rst)
        (!load && (D == 1'b1) && (Q == 1'b1)) |=> (Q == 1'b0)
    );

endmodule