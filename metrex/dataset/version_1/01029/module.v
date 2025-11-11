module count_even(
    input [255:0] in,
    output reg [3:0] out
);

    integer i;
    reg [7:0] even_count;

    always @(*) begin
        even_count = 0;
        for (i = 0; i < 256; i = i + 2) begin
            if (in[i]) begin
                even_count = even_count + 1;
            end
        end
        out = even_count[3:0];
    end

endmodule