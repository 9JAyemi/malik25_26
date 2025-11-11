module boothMultiplier(
    input [3:0] multiplicand,
    input [3:0] multiplier,
    output reg [7:0] product,
    input clock,
    input reset
    );

    reg [3:0] A, Q, M;
    reg Q_1;
    reg [3:0] count;

    wire [3:0] sum, difference;

    always @(posedge clock)
    begin
        if (reset) begin
            A <= 4'b0;      
            M <= multiplicand;
            Q <= multiplier;
            Q_1 <= 1'b0;      
            count <= 3'b0;
        end
        else begin
            case ({Q[0], Q_1})
                2'b01 : {A, Q, Q_1} <= {sum[3], sum, Q};
                2'b10 : {A, Q, Q_1} <= {difference[3], difference, Q};
                default: {A, Q, Q_1} <= {A[3], A, Q};
            endcase
            count <= count + 1;
            if (count == 4) begin
                product <= {A, Q};
            end
        end
    end

    alu adder (.A(A), .B(M), .cin(1'b0), .sum(sum));
    alu subtracter (.A(A), .B(~M), .cin(1'b1), .sum(difference));

endmodule

module alu(
    input [3:0] A,
    input [3:0] B,
    input cin,
    output [3:0] sum
    );

    assign sum = A + B + cin;

endmodule