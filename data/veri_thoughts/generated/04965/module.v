module dff_with_set_reset(q, qbar, clock, data, PREbar, CLRbar);
    input  clock, data, PREbar, CLRbar;
    output q, qbar;
    reg    q;

    always @(posedge clock) begin
        if (PREbar == 0) begin
            q <= 1'b1;
        end else if (CLRbar == 0) begin
            q <= 1'b0;
        end else begin
            q <= data;
        end
    end

    assign qbar = ~q;

endmodule