module shift_register_assertions (
    input logic [3:0] D0,
    input logic [3:0] D1,
    input logic [3:0] D2,
    input logic [3:0] D3,
    input logic CLK,
    input logic LOAD,
    input logic RESET,
    input logic [3:0] Q0,
    input logic [3:0] Q1,
    input logic [3:0] Q2,
    input logic [3:0] Q3
);

    // Reset clears Q0 by the next clock sample.
    reset_clears_Q0: assert property (
        @(posedge CLK)
        RESET |=> (Q0 == 4'b0000)
    );

    // Reset clears Q1 by the next clock sample.
    reset_clears_Q1: assert property (
        @(posedge CLK)
        RESET |=> (Q1 == 4'b0000)
    );

    // Reset clears Q2 by the next clock sample.
    reset_clears_Q2: assert property (
        @(posedge CLK)
        RESET |=> (Q2 == 4'b0000)
    );

    // Reset clears Q3 by the next clock sample.
    reset_clears_Q3: assert property (
        @(posedge CLK)
        RESET |=> (Q3 == 4'b0000)
    );

    // LOAD causes Q0 to capture D0.
    load_captures_D0_into_Q0: assert property (
        @(posedge CLK) disable iff (RESET)
        LOAD |=> (Q0 == $past(D0))
    );

    // LOAD causes Q1 to capture D1.
    load_captures_D1_into_Q1: assert property (
        @(posedge CLK) disable iff (RESET)
        LOAD |=> (Q1 == $past(D1))
    );

    // LOAD causes Q2 to capture D2.
    load_captures_D2_into_Q2: assert property (
        @(posedge CLK) disable iff (RESET)
        LOAD |=> (Q2 == $past(D2))
    );

    // LOAD causes Q3 to capture D3.
    load_captures_D3_into_Q3: assert property (
        @(posedge CLK) disable iff (RESET)
        LOAD |=> (Q3 == $past(D3))
    );

    // Shift mode moves Q1 into Q0.
    shift_moves_Q1_into_Q0: assert property (
        @(posedge CLK) disable iff (RESET)
        !LOAD |=> (Q0 == $past(Q1))
    );

    // Shift mode moves Q2 into Q1.
    shift_moves_Q2_into_Q1: assert property (
        @(posedge CLK) disable iff (RESET)
        !LOAD |=> (Q1 == $past(Q2))
    );

    // Shift mode moves Q3 into Q2.
    shift_moves_Q3_into_Q2: assert property (
        @(posedge CLK) disable iff (RESET)
        !LOAD |=> (Q2 == $past(Q3))
    );

    // Shift mode moves D0 into Q3.
    shift_moves_D0_into_Q3: assert property (
        @(posedge CLK) disable iff (RESET)
        !LOAD |=> (Q3 == $past(D0))
    );

endmodule