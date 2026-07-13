module priority_arbiter_sva (
    input logic clk,

    input logic src0_arb_atom_q,
    input logic src0_arb_req_q,
    input logic src1_arb_atom_q,
    input logic src1_arb_req_q,
    input logic src2_arb_atom_q,
    input logic src2_arb_req_q,
    input logic src3_arb_atom_q,
    input logic src3_arb_req_q,
    input logic src4_arb_atom_q,
    input logic src4_arb_req_q,
    input logic src5_arb_atom_q,
    input logic src5_arb_req_q,
    input logic src6_arb_atom_q,
    input logic src6_arb_req_q,
    input logic src7_arb_atom_q,
    input logic src7_arb_req_q,

    input logic arb_src0_grant_a,
    input logic arb_src1_grant_a,
    input logic arb_src2_grant_a,
    input logic arb_src3_grant_a,
    input logic arb_src4_grant_a,
    input logic arb_src5_grant_a,
    input logic arb_src6_grant_a,
    input logic arb_src7_grant_a
);
    // DUT is purely combinational (no reset); assertions sampled on external clk.

    // Grant0 equals req0 & atom0.
    check_grant0_logic: assert property (
        @(posedge clk) arb_src0_grant_a == (src0_arb_req_q && src0_arb_atom_q)
    );

    // Grant1 equals req1 & atom1 & !atom0.
    check_grant1_logic: assert property (
        @(posedge clk) arb_src1_grant_a == (src1_arb_req_q && src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grant2 equals req2 & atom2 & !atom1 & !atom0.
    check_grant2_logic: assert property (
        @(posedge clk) arb_src2_grant_a == (src2_arb_req_q && src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grant3 equals req3 & atom3 & !atom2 & !atom1 & !atom0.
    check_grant3_logic: assert property (
        @(posedge clk) arb_src3_grant_a == (src3_arb_req_q && src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grant4 equals req4 & atom4 & !atom3..0.
    check_grant4_logic: assert property (
        @(posedge clk) arb_src4_grant_a == (src4_arb_req_q && src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grant5 equals req5 & atom5 & !atom4..0.
    check_grant5_logic: assert property (
        @(posedge clk) arb_src5_grant_a == (src5_arb_req_q && src5_arb_atom_q && !src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grant6 equals req6 & atom6 & !atom5..0.
    check_grant6_logic: assert property (
        @(posedge clk) arb_src6_grant_a == (src6_arb_req_q && src6_arb_atom_q && !src5_arb_atom_q && !src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grant7 equals req7 & atom7 & !atom6..0.
    check_grant7_logic: assert property (
        @(posedge clk) arb_src7_grant_a == (src7_arb_req_q && src7_arb_atom_q && !src6_arb_atom_q && !src5_arb_atom_q && !src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q)
    );

    // Grants are mutually exclusive (0 or 1 set).
    check_grant_mutex: assert property (
        @(posedge clk) $onehot0({arb_src7_grant_a,arb_src6_grant_a,arb_src5_grant_a,arb_src4_grant_a,arb_src3_grant_a,arb_src2_grant_a,arb_src1_grant_a,arb_src0_grant_a})
    );

    // If no atoms are set, no grants are set.
    check_no_atom_no_grant: assert property (
        @(posedge clk)
            !(src0_arb_atom_q || src1_arb_atom_q || src2_arb_atom_q || src3_arb_atom_q ||
              src4_arb_atom_q || src5_arb_atom_q || src6_arb_atom_q || src7_arb_atom_q)
            |-> !(arb_src0_grant_a || arb_src1_grant_a || arb_src2_grant_a || arb_src3_grant_a ||
                  arb_src4_grant_a || arb_src5_grant_a || arb_src6_grant_a || arb_src7_grant_a)
    );

endmodule