
module top_module (
    input CLK,
    input UP_DOWN,
    input RESET,
    input [3:0] gray,
    output reg [3:0] OUT
);

wire [3:0] binary;
wire [3:0] counter;
wire [3:0] sum;

gray_to_binary gray_to_binary_inst (
    .gray(gray),
    .binary(binary)
);

up_down_counter up_down_counter_inst (
    .CLK(CLK),
    .UP_DOWN(UP_DOWN),
    .RESET(RESET),
    .OUT(counter)
);

functional_module functional_module_inst (
    .binary(binary),
    .counter(counter),
    .sum(sum)
);

always @ (posedge CLK) begin
    if (RESET) begin
        OUT <= 4'b0000;
    end else begin
        if (UP_DOWN) begin
            OUT <= OUT + 4'b0001;
        end else begin
            OUT <= OUT - 4'b0001;
        end
    end
end

endmodule
module gray_to_binary (
    input [3:0] gray,
    output reg [3:0] binary
);

always @* begin
    binary[3] = gray[3];
    binary[2] = binary[3] ^ gray[2];
    binary[1] = binary[2] ^ gray[1];
    binary[0] = binary[1] ^ gray[0];
end

endmodule
module up_down_counter (
    input CLK,
    input UP_DOWN,
    input RESET,
    output reg [3:0] OUT
);

always @ (posedge CLK) begin
    if (RESET) begin
        OUT <= 4'b0000;
    end else begin
        if (UP_DOWN) begin
            OUT <= OUT + 4'b0001;
        end else begin
            OUT <= OUT - 4'b0001;
        end
    end
end

endmodule
module functional_module (
    input [3:0] binary,
    input [3:0] counter,
    output reg [3:0] sum
);

always @* begin
    sum = binary + counter;
end

endmodule