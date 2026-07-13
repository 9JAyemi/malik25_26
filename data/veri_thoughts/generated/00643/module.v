
module arriaiigz_ram_pulse_generator (
    input  clk,   // clock
    input  ena,   // pulse enable
    output pulse, // pulse
    output cycle  // delayed clock
);

reg pulse_reg = 1'b0;
reg cycle_reg = 1'b0;

// Delay the clock signal
always @(posedge clk)
    cycle_reg <= clk;

// Generate the pulse signal
always @(posedge cycle_reg)
    if (ena)
        pulse_reg <= 1'b1;
    else
        pulse_reg <= 1'b0;

assign pulse = pulse_reg;
assign cycle = cycle_reg;

endmodule