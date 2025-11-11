// SVA for ham_15_11_decoder and wrapper. Bind these checkers in your testbench.

module ham_15_11_decoder_sva;
  // This module is bound into ham_15_11_decoder's scope, so it can see c,q,pb,s,temp,inputs.

  function automatic bit any_x15(input logic [14:0] v);
    return $isunknown(v);
  endfunction

  function automatic logic [10:0] pack_q(input logic [14:0] v);
    // q mapping after correction
    return { v[14], v[13], v[12], v[11], v[10], v[9], v[8], v[6], v[5], v[4], v[2] };
  endfunction

  logic [3:0] pb_exp, s_exp;
  logic [3:0] s_val, temp_exp;
  logic [14:0] corr;
  logic [10:0] q_ref;

  always_comb begin
    // Golden parity and syndrome
    pb_exp[0]=c[2]^c[4]^c[6]^c[8]^c[10]^c[12]^c[14];
    pb_exp[1]=c[2]^c[5]^c[6]^c[9]^c[10]^c[13]^c[14];
    pb_exp[2]=c[4]^c[5]^c[6]^c[11]^c[12]^c[13]^c[14];
    pb_exp[3]=c[8]^c[9]^c[10]^c[11]^c[12]^c[13]^c[14];

    s_exp[0]=c[0]^pb_exp[0];
    s_exp[1]=c[1]^pb_exp[1];
    s_exp[2]=c[3]^pb_exp[2];
    s_exp[3]=c[7]^pb_exp[3];

    s_val   = {s_exp[3],s_exp[2],s_exp[1],s_exp[0]};
    temp_exp= (s_val==0) ? 4'd15 : (s_val-1);

    // Golden correction and q
    corr = c;
    if (s_val != 0) corr[s_val-1] = ~c[s_val-1];
    q_ref = pack_q(corr);

    // Assertions (skip when inputs are X/Z)
    if (!any_x15(c)) begin
      assert (pb   === pb_exp)    else $error("ham_15_11_decoder: pb mismatch exp=%0b got=%0b", pb_exp, pb);
      assert (s    === s_exp)     else $error("ham_15_11_decoder: s mismatch exp=%0b got=%0b", s_exp, s);
      assert (temp === temp_exp)  else $error("ham_15_11_decoder: temp mismatch exp=%0d got=%0d", temp_exp, temp);
      assert (q    === q_ref)     else $error("ham_15_11_decoder: q mismatch vs corrected mapping");

      // No-error case keeps original data bits
      if (s_val == 0) assert (q === pack_q(c)) else $error("No-error case incorrect");

      // Parity-only error should not affect q
      if (s_val inside {4'd1,4'd2,4'd4,4'd8}) assert (q === pack_q(c)) else $error("Parity-bit error modified data");

      // q must not be X/Z when c is known
      assert (!$isunknown(q)) else $error("q has X/Z for known c");
    end

    // Functional coverage of all syndromes
    if (!any_x15(c)) begin
      cover (s_val == 4'd0);
      cover (s_val == 4'd1);
      cover (s_val == 4'd2);
      cover (s_val == 4'd3);
      cover (s_val == 4'd4);
      cover (s_val == 4'd5);
      cover (s_val == 4'd6);
      cover (s_val == 4'd7);
      cover (s_val == 4'd8);
      cover (s_val == 4'd9);
      cover (s_val == 4'd10);
      cover (s_val == 4'd11);
      cover (s_val == 4'd12);
      cover (s_val == 4'd13);
      cover (s_val == 4'd14);
      cover (s_val == 4'd15);
      cover (s_val inside {4'd1,4'd2,4'd4,4'd8}); // parity-bit errors
      cover (s_val inside {4'd3,4'd5,4'd6,4'd7,4'd9,4'd10,4'd11,4'd12,4'd13,4'd14,4'd15}); // data-bit errors
    end
  end
endmodule

bind ham_15_11_decoder ham_15_11_decoder_sva sva_h1511();



// Optional: wrapper-level SVA to ensure wiring correctness end-to-end
module ham_decoder_sva;
  // Bound into ham_decoder; uses cc/qq
  function automatic bit any_x15(input logic [14:0] v);
    return $isunknown(v);
  endfunction
  function automatic logic [10:0] pack_q(input logic [14:0] v);
    return { v[14], v[13], v[12], v[11], v[10], v[9], v[8], v[6], v[5], v[4], v[2] };
  endfunction
  logic [3:0] pb_exp, s_exp;
  logic [3:0] s_val;
  logic [14:0] corr;
  logic [10:0] qq_ref;

  always_comb begin
    pb_exp[0]=cc[2]^cc[4]^cc[6]^cc[8]^cc[10]^cc[12]^cc[14];
    pb_exp[1]=cc[2]^cc[5]^cc[6]^cc[9]^cc[10]^cc[13]^cc[14];
    pb_exp[2]=cc[4]^cc[5]^cc[6]^cc[11]^cc[12]^cc[13]^cc[14];
    pb_exp[3]=cc[8]^cc[9]^cc[10]^cc[11]^cc[12]^cc[13]^cc[14];
    s_exp[0]=cc[0]^pb_exp[0];
    s_exp[1]=cc[1]^pb_exp[1];
    s_exp[2]=cc[3]^pb_exp[2];
    s_exp[3]=cc[7]^pb_exp[3];
    s_val   = {s_exp[3],s_exp[2],s_exp[1],s_exp[0]};

    corr = cc;
    if (s_val != 0) corr[s_val-1] = ~cc[s_val-1];
    qq_ref = pack_q(corr);

    if (!any_x15(cc)) begin
      assert (qq === qq_ref) else $error("ham_decoder wrapper: qq mismatch vs golden");
      cover (s_val == 0);
      cover (s_val inside {4'd1,4'd2,4'd4,4'd8});
      cover (s_val inside {4'd3,4'd5,4'd6,4'd7,4'd9,4'd10,4'd11,4'd12,4'd13,4'd14,4'd15});
    end
  end
endmodule

bind ham_decoder ham_decoder_sva sva_wrapper();