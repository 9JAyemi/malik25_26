module sync2r_1 ( clk, preset, d, q );
    input clk;
    input preset;
    input d;
    output q;

    reg q1, q2; // two registers

    always @(posedge clk or posedge preset) begin
        if (preset) begin
            q1 <= 1'b0; // reset to known state
            q2 <= 1'b0;
        end else begin
            q1 <= d; // first register triggered by rising edge
            q2 <= q1; // second register triggered by falling edge
        end
    end

    assign q = q2; // output synchronized data signal
endmodule