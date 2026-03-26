module priority_encoder_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic [1:0] X
);

    // A4 has highest priority and forces X to 11.
    check_a4_priority: assert property (
        @(posedge clk) A4 |-> (X == 2'b11)
    );

    // A3 is encoded as 10 when A4 is low.
    check_a3_priority: assert property (
        @(posedge clk) (!A4 && A3) |-> (X == 2'b10)
    );

    // A2 is encoded as 01 when A4 and A3 are low.
    check_a2_priority: assert property (
        @(posedge clk) (!A4 && !A3 && A2) |-> (X == 2'b01)
    );

    // A1 is encoded as 00 when all higher-priority inputs are low.
    check_a1_encoding: assert property (
        @(posedge clk) (!A4 && !A3 && !A2 && A1) |-> (X == 2'b00)
    );

    // No asserted inputs produce 00.
    check_no_input_encoding: assert property (
        @(posedge clk) (!A4 && !A3 && !A2 && !A1) |-> (X == 2'b00)
    );

    // Output 11 can only occur when A4 is asserted.
    check_x11_source: assert property (
        @(posedge clk) (X == 2'b11) |-> A4
    );

    // Output 10 can only occur when A3 is asserted and A4 is low.
    check_x10_source: assert property (
        @(posedge clk) (X == 2'b10) |-> (!A4 && A3)
    );

    // Output 01 can only occur when A2 is asserted and higher inputs are low.
    check_x01_source: assert property (
        @(posedge clk) (X == 2'b01) |-> (!A4 && !A3 && A2)
    );

    // Output 00 requires all higher-priority inputs to be low.
    check_x00_source: assert property (
        @(posedge clk) (X == 2'b00) |-> (!A4 && !A3 && !A2)
    );

    // X matches the priority-encoded value of the inputs.
    check_full_function: assert property (
        @(posedge clk) X == (A4 ? 2'b11 : (A3 ? 2'b10 : (A2 ? 2'b01 : 2'b00)))
    );

endmodule