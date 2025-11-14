
module top_module (
    input  [15:0] A,
    input  [15:0] B,
    input         clk,
    input         reset,
    output reg [15:0] Y
);

    // Instantiate the comparator module
    comparator_4bit comparator (
        .A(A[15:12]),
        .B(B[15:12]),
        .GT(select)
    );

    // Instantiate the barrel shifter module
    barrel_shifter_16bit shifter (
        .A(select ? B : A),
        .shift_amount(select ? B[11:8] : A[11:8]),
        .Y(shifted_data)
    );

    // Instantiate the priority encoder module
    priority_encoder_4bit encoder (
        .A(select ? B[3:0] : A[3:0]),
        .Y(shift_amount)
    );

    // Output the shifted data
    always @ (posedge clk) begin
        if (reset) begin
            Y <= 16'b0;
        end else begin
            Y <= shifted_data;
        end
    end

    // Internal signals
    wire [15:0] shifted_data;
    wire [1:0] shift_amount;
    wire select;

endmodule
module comparator_4bit (
    input  [3:0] A,
    input  [3:0] B,
    output reg GT
);

    always @ (*) begin
        if (A > B) begin
            GT = 1;
        end else begin
            GT = 0;
        end
    end

endmodule
module barrel_shifter_16bit (
    input  [15:0] A,
    input  [3:0] shift_amount,
    output reg [15:0] Y
);

    always @ (*) begin
        case (shift_amount)
            4'b0000: Y = A;
            4'b0001: Y = {A[14], A[15:1]};
            4'b0010: Y = {A[13], A[15:2]};
            4'b0011: Y = {A[12], A[15:3]};
            4'b0100: Y = {A[11], A[15:4]};
            4'b0101: Y = {A[10], A[15:5]};
            4'b0110: Y = {A[9], A[15:6]};
            4'b0111: Y = {A[8], A[15:7]};
            4'b1000: Y = {A[7], A[15:8]};
            4'b1001: Y = {A[6], A[15:9]};
            4'b1010: Y = {A[5], A[15:10]};
            4'b1011: Y = {A[4], A[15:11]};
            4'b1100: Y = {A[3], A[15:12]};
            4'b1101: Y = {A[2], A[15:13]};
            4'b1110: Y = {A[1], A[15:14]};
            4'b1111: Y = {A[0], A[15:15]};
            default: Y = A;
        endcase
    end

endmodule
module priority_encoder_4bit (
    input  [3:0] A,
    output reg [1:0] Y
);

    always @ (*) begin
        casex (A)
            4'b0001: Y = 2'b00;
            4'b0010: Y = 2'b01;
            4'b0100: Y = 2'b10;
            4'b1000: Y = 2'b11;
            default: Y = 2'b00;
        endcase
    end

endmodule