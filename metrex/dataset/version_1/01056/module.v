
module binary_to_bcd (
    input [3:0] binary_in,
    output reg [15:0] bcd_out
);

reg [3:0] bcd_temp;
reg [3:0] binary_temp;
reg [2:0] bcd_count;

always @ (*) begin
    bcd_temp = 0;
    bcd_count = 0;
    binary_temp = binary_in;
    for (bcd_count = 0; bcd_count < 4; bcd_count = bcd_count + 1) begin
        if (binary_temp >= 4'b1010) begin
            bcd_temp = bcd_temp + 4'b0001;
            binary_temp = binary_temp - 4'b1010;
        end
        else if (binary_temp >= 4'b1000) begin
            bcd_temp = bcd_temp + 4'b0001;
            binary_temp = binary_temp - 4'b1000;
        end
        else if (binary_temp >= 4'b0100) begin
            bcd_temp = bcd_temp + 4'b0010;
            binary_temp = binary_temp - 4'b0100;
        end
        else if (binary_temp >= 4'b0010) begin
            bcd_temp = bcd_temp + 4'b0010;
            binary_temp = binary_temp - 4'b0010;
        end
        else if (binary_temp >= 4'b0001) begin
            bcd_temp = bcd_temp + 4'b0100;
            binary_temp = binary_temp - 4'b0001;
        end
    end
end

always @ (bcd_count) begin
    case (bcd_count)
        3'b000: bcd_out = {8'b0, bcd_temp};
        3'b001: bcd_out = {7'b0, bcd_temp};
        3'b010: bcd_out = {6'b0, bcd_temp};
        3'b011: bcd_out = {5'b0, bcd_temp};
        3'b100: bcd_out = {4'b0, bcd_temp};
        default: bcd_out = 16'b0;
    endcase
end

endmodule