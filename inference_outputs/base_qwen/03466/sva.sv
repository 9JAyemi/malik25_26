module sync_signal_sva (
    input logic clk,
    input logic in,
    output logic out,
    output logic falling,
    output logic rising
);
    reg [2:0] shiftreg;

    initial begin
        shiftreg <= 0;
    end

    always @(posedge clk) begin
        shiftreg[2:1] <= shiftreg[1:0];
        shiftreg[0] <= in;
    end

    assign out = shiftreg[1];
    assign falling = shiftreg[2] & ~shiftreg[1];
    assign rising = ~shiftreg[2] & shiftreg[1];

    // Ensure shiftreg is properly updated on each clock edge
    shiftreg_update: assert property (
        @(posedge clk) disable iff (!clk) shiftreg[2:0] == {shiftreg[1:0], in}
    );

    // Ensure out is synchronized with the middle bit of shiftreg
    out_sync: assert property (
        @(posedge clk) disable iff (!clk) out == shiftreg[1]
    );

    // Ensure falling edge is detected correctly
    falling_edge: assert property (
        @(posedge clk) disable iff (!clk) falling |-> shiftreg[2] & ~shiftreg[1]
    );

    // Ensure rising edge is detected correctly
    rising_edge: assert property (
        @(posedge clk) disable iff (!clk) rising |-> ~shiftreg[2] & shiftreg[1]
    );

    // Ensure shiftreg is reset to 0 on each clock edge
    shiftreg_reset: assert property (
        @(posedge clk) disable iff (!clk) shiftreg == 0
    );

    // Ensure out is reset to 0 on each clock edge
    out_reset: assert property (
        @(posedge clk) disable iff (!clk) out == 0
    );

    // Ensure falling is reset to 0 on each clock edge
    falling_reset: assert property (
        @(posedge clk) disable iff (!clk) falling == 0
    );

    // Ensure rising is reset to 0 on each clock edge
    rising_reset: assert property (
        @(posedge clk) disable iff (!clk) rising == 0
    );
endmodule