module shift_register(
    input clk,
    input stb,
    input di,
    output do
);
    parameter integer DIN_N = 256;
    parameter integer DOUT_N = 256;

    reg [DIN_N-1:0] din_shr; // Shift register for input
    reg [DOUT_N-1:0] dout_shr; // Shift register for output

    always @(posedge clk) begin
        if (stb) begin
            // On strobe signal, load din_shr with the current serial input at the LSB
            din_shr <= {din_shr[DIN_N-2:0], di};
        end
        // Shift the most significant bit of din_shr into dout_shr on every clock
        dout_shr <= {dout_shr[DOUT_N-2:0], din_shr[DIN_N-1]};
    end

    assign do = dout_shr[DOUT_N-1];
endmodule
