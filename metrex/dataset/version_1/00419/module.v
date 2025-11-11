module add_sub (
    input [3:0] A,
    input [3:0] B,
    input C,
    output reg [3:0] Q
);

reg [3:0] sum_reg;
reg [3:0] sub_reg;

always @ (posedge C) begin // Fixed the clock signal
    if (C == 1'b1) begin // Addition
        sum_reg <= A + B;
    end else begin // Subtraction
        sub_reg <= A - B;
    end
end

always @ (posedge C) begin // Fixed the clock signal
    if (C == 1'b1) begin // Addition
        Q <= sum_reg;
    end else begin // Subtraction
        Q <= sub_reg;
    end
end

endmodule