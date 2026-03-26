module DNA_PORT (
    output DOUT,
    input CLK,
    input DIN,
    input READ,
    input SHIFT
);

    parameter [56:0] SIM_DNA_VALUE = 57'h0;

    localparam MAX_DNA_BITS = 57;
    localparam MSB_DNA_BITS = MAX_DNA_BITS - 1;

    reg [MSB_DNA_BITS:0] dna_val = SIM_DNA_VALUE;
    reg dout_out;

    always @(posedge CLK) begin
        if (READ) begin
            dout_out <= 1'b1;
            dna_val <= SIM_DNA_VALUE;
        end else if (SHIFT) begin
            dout_out <= dna_val[MSB_DNA_BITS];
            dna_val <= {dna_val[MSB_DNA_BITS-1:0], DIN};
        end
    end

    assign DOUT = dout_out;

endmodule