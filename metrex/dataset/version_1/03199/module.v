module add_sub (
    input [7:0] a,
    input [7:0] b,
    input add_sub_ctrl,
    output reg [7:0] result,
    output reg overflow
);

    reg [8:0] temp; // temporary register for overflow detection

    always @(*) begin
        if (add_sub_ctrl) begin // subtraction
            temp = {1'b0, a} - {1'b1, b}; // 2's complement subtraction
            result = temp[7:0];
            overflow <= temp[8] ^ temp[7]; // overflow if MSB of temp is not equal to MSB of result
        end else begin // addition
            temp = a + b;
            result = temp[7:0];
            overflow <= temp[8]; // overflow if MSB of temp is 1
        end
    end

endmodule