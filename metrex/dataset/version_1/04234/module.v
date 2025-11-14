module my_delayed_clk (
    output reg GCLK,
    input GATE,
    input CLK,
    input VPWR,
    input VGND,
    input RST
);

    parameter DELAY_CYCLES = 10;

    reg [DELAY_CYCLES-1:0] delay_counter;
    reg delayed_clk;

    always @(posedge CLK or negedge RST) begin
        if (!RST) begin
            delay_counter <= 0;
            delayed_clk <= 0;
        end else if (GATE) begin
            if (delay_counter == DELAY_CYCLES-1) begin
                delayed_clk <= 1;
            end else begin
                delayed_clk <= 0;
            end
            delay_counter <= delay_counter + 1;
        end
    end

    always @(posedge CLK or negedge RST) begin
        if (!RST) begin
            GCLK <= 0;
        end else begin
            GCLK <= delayed_clk;
        end
    end

endmodule