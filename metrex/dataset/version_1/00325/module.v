
module ddr_clkout (pad, clk);
input clk;
output pad;

reg sync_clk;
wire clk_out;
reg [7:0] count;
integer temp,flag1,flag2;

// First stage of synchronizer
reg sync_d1;
always @(posedge clk)
    sync_d1 <= clk;

// Second stage of synchronizer
reg sync_d2;
always @(posedge sync_clk)
    sync_d2 <= sync_d1;

// Counter to generate clock signal
always @(posedge sync_clk) begin
    if (count == 8'hFF)
        count <= 0;
    else
        count <= count + 1;
end

// Output clock signal
assign clk_out = count[6];

// D flip-flop to generate 50% duty cycle
reg d, d_temp;
always @(posedge clk_out)
    d <= ~d;

// Output to pad
assign pad = d;

// Synchronize input clock signal
always @(posedge clk)
    sync_clk <= ~sync_clk;

endmodule