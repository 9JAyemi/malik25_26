module up_down_counter_4bit_sva (
    input logic       clk,
    input logic       Up,
    input logic       Down,
    input logic [3:0] Q
);

    // Up increments Q when it is not at the maximum value.
    check_up_increment: assert property (
        @(posedge clk) disable iff (1'b0)
        Up && (Q != 4'hF) |=> (Q == ($past(Q) + 4'h1))
    );

    // Up wraps Q from 15 back to 0.
    check_up_wrap: assert property (
        @(posedge clk) disable iff (1'b0)
        Up && (Q == 4'hF) |=> (Q == 4'h0)
    );

    // Down decrements Q when Up is low and Q is not at zero.
    check_down_decrement: assert property (
        @(posedge clk) disable iff (1'b0)
        !Up && Down && (Q != 4'h0) |=> (Q == ($past(Q) - 4'h1))
    );

    // Down wraps Q from 0 back to 15 when Up is low.
    check_down_wrap: assert property (
        @(posedge clk) disable iff (1'b0)
        !Up && Down && (Q == 4'h0) |=> (Q == 4'hF)
    );

    // Q holds its value when neither Up nor Down is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (1'b0)
        !Up && !Down |=> (Q == $past(Q))
    );

endmodule