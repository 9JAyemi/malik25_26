module clock_gate_4bit_up_counter(
    input CLK,
    input EN,
    input TE,
    output reg ENCLK
);

reg prev_EN;

always @(posedge CLK) begin
    if (TE) begin
        ENCLK <= 1'b0; // reset the counter
    end else if (EN && !prev_EN) begin
        ENCLK <= 1'b1; // enable the counter
    end else begin
        ENCLK <= 1'b0; // disable the counter
    end
    prev_EN <= EN;
end

endmodule