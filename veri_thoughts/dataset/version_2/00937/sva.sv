module two_input_logic_sva (
    input logic A,
    input logic B,
    input logic X
);
    // X equals XNOR of A and B
    check_x_equals_xnor: assert property (
        @(posedge A or negedge A or posedge B or negedge B) X == ~(A ^ B)
    );

    // Truth table: A=0, B=0 => X=1
    check_tt_a0b0: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!A && !B) |-> (X == 1'b1)
    );

    // Truth table: A=1, B=1 => X=1
    check_tt_a1b1: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A && B) |-> (X == 1'b1)
    );

    // Truth table: A=1, B=0 => X=0
    check_tt_a1b0: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A && !B) |-> (X == 1'b0)
    );

    // Truth table: A=0, B=1 => X=0
    check_tt_a0b1: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!A && B) |-> (X == 1'b0)
    );
endmodule