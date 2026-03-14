
module priority_arbiter(
    input src0_arb_atom_q,
    input src0_arb_req_q,
    input src1_arb_atom_q,
    input src1_arb_req_q,
    input src2_arb_atom_q,
    input src2_arb_req_q,
    input src3_arb_atom_q,
    input src3_arb_req_q,
    input src4_arb_atom_q,
    input src4_arb_req_q,
    input src5_arb_atom_q,
    input src5_arb_req_q,
    input src6_arb_atom_q,
    input src6_arb_req_q,
    input src7_arb_atom_q,
    input src7_arb_req_q,
    output arb_src0_grant_a,
    output arb_src1_grant_a,
    output arb_src2_grant_a,
    output arb_src3_grant_a,
    output arb_src4_grant_a,
    output arb_src5_grant_a,
    output arb_src6_grant_a,
    output arb_src7_grant_a
);

assign arb_src0_grant_a = src0_arb_req_q && src0_arb_atom_q;
assign arb_src1_grant_a = src1_arb_req_q && src1_arb_atom_q && !src0_arb_atom_q;
assign arb_src2_grant_a = src2_arb_req_q && src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q;
assign arb_src3_grant_a = src3_arb_req_q && src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q;
assign arb_src4_grant_a = src4_arb_req_q && src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q;
assign arb_src5_grant_a = src5_arb_req_q && src5_arb_atom_q && !src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q;
assign arb_src6_grant_a = src6_arb_req_q && src6_arb_atom_q && !src5_arb_atom_q && !src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q;
assign arb_src7_grant_a = src7_arb_req_q && src7_arb_atom_q && !src6_arb_atom_q && !src5_arb_atom_q && !src4_arb_atom_q && !src3_arb_atom_q && !src2_arb_atom_q && !src1_arb_atom_q && !src0_arb_atom_q;

endmodule