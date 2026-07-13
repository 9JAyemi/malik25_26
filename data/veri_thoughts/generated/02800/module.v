module twos_complement (
    input [3:0] binary,
    output reg [3:0] twos_comp
);

    always @(*) begin
        twos_comp = ~binary + 1;
    end

endmodule