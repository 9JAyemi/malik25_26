module up_down_counter_4bit_sva (
    input logic clk,
    input logic Up,
    input logic Down,
    input logic [3:0] Q
);
    ///// Up and Down control /////
    // Up can only transition from LOW to HIGH when Q is not at its maximum value.
    up_transition: assert property (
        @(posedge clk) disable iff (!clk) $rose(Up) |-> (Q != 4'b1111)
    );
    // Down can only transition from LOW to HIGH when Q is not at its minimum value.
    down_transition: assert property (
        @(posedge clk) disable iff (!clk) $rose(Down) |-> (Q != 4'b0000)
    );
    // Up and Down cannot both be HIGH at the same time.
    up_down_xor: assert property (
        @(posedge clk) disable iff (!clk) !(Up && Down)
    );
    // Q can only transition when either Up or Down is HIGH.
    q_transition: assert property (
        @(posedge clk) disable iff (!clk) (Q == $past(Q)) |-> !(Up || Down)
    );
    // Q increments when Up is HIGH and Q is not at its maximum value.
    q_increment: assert property (
        @(posedge clk) disable iff (!clk) (Up && (Q != 4'b1111)) |-> (Q == $past(Q) + 1)
    );
    // Q decrements when Down is HIGH and Q is not at its minimum value.
    q_decrement: assert property (
        @(posedge clk) disable iff (!clk) (Down && (Q != 4'b0000)) |-> (Q == $past(Q) - 1)
    );
    // Q wraps around to 0 when it reaches its maximum value.
    q_wrap_up: assert property (
        @(posedge clk) disable iff (!clk) (Q == 4'b1111) |-> (Q == 4'b0000)
    );
    // Q wraps around to 15 when it reaches its minimum value.
    q_wrap_down: assert property (
        @(posedge clk) disable iff (!clk) (Q == 4'b0000) |-> (Q == 4'b1111)
    );
    // Q remains unchanged when neither Up nor Down is HIGH.
    q_stable: assert property (
        @(posedge clk) disable iff (!clk) (!(Up || Down)) |-> (Q == $past(Q))
    );
endmodule