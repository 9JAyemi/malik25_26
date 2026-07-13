module dffe_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] din,
    input logic en,
    input logic se,
    input logic [7:0] si,
    output logic [7:0] q,
    output logic [7:0] so
);
    // Ensure that q is reset to 0 when rst_n is low
    reset_q: assert property (
        @(posedge clk) disable iff (!rst_n) (q == 8'b0)
    ) else $error("q is not reset to 0 when rst_n is low");

    // Ensure that q is updated to si when se is high
    update_q_se: assert property (
        @(posedge clk) disable iff (!rst_n) (se |-> (q == si))
    ) else $error("q is not updated to si when se is high");

    // Ensure that q is updated to din when se is low and en is high
    update_q_en: assert property (
        @(posedge clk) disable iff (!rst_n) (!se && en |-> (q == din))
    ) else $error("q is not updated to din when se is low and en is high");

    // Ensure that so is always equal to q
    so_equal_q: assert property (
        @(posedge clk) disable iff (!rst_n) (so == q)
    ) else $error("so is not equal to q");

endmodule