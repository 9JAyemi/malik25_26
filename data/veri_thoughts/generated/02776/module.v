
module clock_gate_high_register_add (
    input CLK,
    input EN,
    input TE,
    output reg ENCLK
);

    always @ (posedge CLK) begin
        if (EN) begin
            ENCLK <= TE;
        end
    end

endmodule