
module priority_encoder (
    input [7:0] I,
    output reg EN,
    output reg V,
    output reg [2:0] Q
);

    parameter WIDTH = 8;
    integer i;

    always @(*) begin
        if (|I) begin
            EN = 1;
            V = (|I) & (~&I);
            for (i = 0; i < WIDTH; i = i + 1) begin
                if (I[i]) begin
                    Q = i + 1'b1;
                end
            end
        end
        else begin
            EN = 0;
            V = 0;
            Q = 0;
        end
    end

endmodule