module top_module_sva (
    input logic clk,
    input logic reset, // Synchronous active-high reset
    input logic up_down,
    input logic enable,
    output logic [7:0] q // 8-bit output from the functional module
);

    wire [1:0] counter_out;
    wire [1:0] gray_out;

    gray_counter counter (
        .clk(clk),
        .reset(reset),
        .up_down(up_down),
        .enable(enable),
        .counter_out(counter_out),
        .gray_out(gray_out)
    );

    functional_module func (
        .counter_out(counter_out),
        .gray_out(gray_out),
        .q(q)
    );

    ///// Counter behavior /////
    // Counter increments when enable is high and up_down is high.
    counter_inc: assert property (
        @(posedge clk) disable iff (reset) (enable && up_down) |-> (counter_out == counter_out + 2'b1)
    );
    // Counter decrements when enable is high and up_down is low.
    counter_dec: assert property (
        @(posedge clk) disable iff (reset) (enable && !up_down) |-> (counter_out == counter_out - 2'b1)
    );
    // Counter remains unchanged when enable is low.
    counter_hold: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> (counter_out == counter_out)
    );

    ///// Gray code behavior /////
    // Gray code output matches the expected values for counter values.
    gray_code_correct: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b00) |-> (gray_out == 2'b00)
    );
    gray_code_correct: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b01) |-> (gray_out == 2'b01)
    );
    gray_code_correct: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b11) |-> (gray_out == 2'b11)
    );
    gray_code_correct: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b10) |-> (gray_out == 2'b10)
    );

    ///// Output behavior /////
    // Output q is correctly formed by concatenating gray_out and counter_out.
    output_correct: assert property (
        @(posedge clk) disable iff (reset) (q == {gray_out, counter_out})
    );

endmodule