module addsub_16bit (
    input [15:0] in0,
    input [15:0] in1,
    input control,
    output reg [15:0] out
);

    always @(*) begin
        if (control) begin
            out <= in0 - in1;
        end else begin
            out <= in0 + in1;
        end
    end

endmodule