
module diff_d2e(
    clk, clrn,  
    wreg, m2reg, shift, aluimm, wmem, wzero, aluc, rd, qa, qb, eximme,
    ewreg, em2reg, eshift, ealuimm, ewmem, ewzero, ealuc, erd, esa, eqa, eqb, eeximme
);
    input clk, clrn;
    input wreg, m2reg, shift, aluimm, wmem, wzero;
    input [3:0] aluc;
    input [4:0] rd;
    input [31:0] qa, qb, eximme;
    
    output ewreg, em2reg, eshift, ealuimm, ewmem, ewzero;
    output [3:0] ealuc;
    output [4:0] erd, esa;
    output [31:0] eqa, eqb, eeximme;
    
    reg [31:0] ewreg_d, em2reg_d, eshift_d, ealuimm_d, ewmem_d, ewzero_d;
    reg [3:0] ealuc_d;
    reg [4:0] erd_d, esa_d;
    reg [31:0] eqa_d, eqb_d, eeximme_d;
    
    always @(posedge clk or negedge clrn) begin
        if (~clrn) begin
            ewreg_d <= 0;
            em2reg_d <= 0;
            eshift_d <= 0;
            ealuimm_d <= 0;
            ewmem_d <= 0;
            ewzero_d <= 0;
            ealuc_d <= 0;
            erd_d <= 0;
            esa_d <= 0;
            eqa_d <= 0;
            eqb_d <= 0;
            eeximme_d <= 0;
        end else begin
            ewreg_d <= wreg;
            em2reg_d <= m2reg;
            eshift_d <= shift;
            ealuimm_d <= aluimm;
            ewmem_d <= wmem;
            ewzero_d <= wzero;
            ealuc_d <= aluc;
            erd_d <= rd;
            esa_d <= 5'b0;
            eqa_d <= qa;
            eqb_d <= qb;
            eeximme_d <= eximme;
        end
    end
    
    assign ewreg = ewreg_d;
    assign em2reg = em2reg_d;
    assign eshift = eshift_d;
    assign ealuimm = ealuimm_d;
    assign ewmem = ewmem_d;
    assign ewzero = ewzero_d;
    assign ealuc = ealuc_d;
    assign erd = erd_d;
    assign esa = esa_d;
    assign eqa = eqa_d;
    assign eqb = eqb_d;
    assign eeximme = eeximme_d;
    
endmodule