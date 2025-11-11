
module shift_register (input clk, stb, di, output [255:0] do);
    localparam integer DIN_N = 256;
    localparam integer DOUT_N = 256;

    reg [DIN_N-1:0] din;
    reg [DOUT_N-1:0] dout;

    reg [DIN_N-1:0] din_shr;
    reg [DOUT_N-1:0] dout_shr;

    always @(posedge clk) begin
        din_shr <= {din_shr, di};
        dout_shr <= {dout_shr, din_shr[DIN_N-1]};
        if (stb) begin
            din <= din_shr;
            dout <= dout_shr;
        end
    end

    assign do = dout;

endmodule
module roi (input ci, s0, output o0);
    assign o0 = ci & s0;
endmodule