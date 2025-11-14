
module unsigned_sqrt (
    input [3:0] num,
    output reg [3:0] sqrt
);

reg [3:0] temp;

integer i;

always @(*) begin
    temp = 0;
    for (i = 3; i >= 0; i = i - 1) begin
        temp = (temp << 1) | (num[i]);
        if (temp >= (i+1)) begin
            temp = temp - (i+1);
            sqrt[i] = 1;
        end else begin
            sqrt[i] = 0;
        end
    end
end

endmodule
