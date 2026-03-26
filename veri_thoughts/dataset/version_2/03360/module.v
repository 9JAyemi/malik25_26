
module d_flip_flop_with_en_and_reset(input D, C, E, R, output Q);
reg Q;

always @(posedge C) begin
    if (R) begin
        Q <= 1'b0;
    end
    else if (E) begin
        Q <= D;
    end
end

endmodule