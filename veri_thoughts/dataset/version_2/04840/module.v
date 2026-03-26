module binary_adder(
    input [3:0] A,
    input [3:0] B,
    input control,
    output reg [3:0] C
);

    always @(*) begin
        if(control == 0) begin
            C = A + B;
        end
        else begin
            C = A - B;
        end
    end

endmodule