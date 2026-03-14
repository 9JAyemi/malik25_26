
module my_inverter (
    output reg Y,
    input  wire in
);

    always @(*) begin
        Y = ~in;
    end

endmodule