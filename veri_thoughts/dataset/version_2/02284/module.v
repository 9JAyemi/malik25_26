
module sky130_fd_sc_hd__or2b (
    input A,
    input B_N,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    reg A_reg;
    reg B_N_reg;
    reg X_reg;

    wire A_stable;
    wire B_N_stable;
    wire X_stable;

    assign A_stable = (A_reg === A);
    assign B_N_stable = (B_N_reg === B_N);
    assign X_stable = (X_reg === X);

    always @(posedge VPWR) begin // Using posedge operator for VPWR
        A_reg <= A;
        B_N_reg <= B_N;
    end

    always @(A or B_N or A_stable or B_N_stable or X_stable) begin
        if (A_stable && B_N_stable) begin
            X_reg <= A | B_N;
        end else begin
            X_reg <= #2 A | B_N;
        end
    end

    assign X = X_reg;

endmodule