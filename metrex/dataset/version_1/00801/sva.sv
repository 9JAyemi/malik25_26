// SVA for denise_spritepriority
// Bindable, concise, and checks functional equivalence, priority, and coverage.

module denise_spritepriority_sva (denise_spritepriority m);

  // Combinational checks
  always @* begin
    // sprgroup correctness
    assert (m.sprgroup[0] == (m.nsprite[1:0] != 2'd0)) else $error("sprgroup[0] mismatch");
    assert (m.sprgroup[1] == (m.nsprite[3:2] != 2'd0)) else $error("sprgroup[1] mismatch");
    assert (m.sprgroup[2] == (m.nsprite[5:4] != 2'd0)) else $error("sprgroup[2] mismatch");
    assert (m.sprgroup[3] == (m.nsprite[7:6] != 2'd0)) else $error("sprgroup[3] mismatch");

    // sprcode allowed values
    assert (m.sprcode inside {3'd1,3'd2,3'd3,3'd4,3'd7}) else $error("sprcode invalid");

    // sprcode priority encoder behavior
    if (m.sprgroup == 4'b0000) assert (m.sprcode == 3'd7) else $error("sprcode != 7 when no groups set");
    if (m.sprgroup[0])                       assert (m.sprcode == 3'd1) else $error("sprcode != 1 for group0");
    if (!m.sprgroup[0] && m.sprgroup[1])     assert (m.sprcode == 3'd2) else $error("sprcode != 2 for group1");
    if (!m.sprgroup[0] && !m.sprgroup[1] &&
        m.sprgroup[2])                       assert (m.sprcode == 3'd3) else $error("sprcode != 3 for group2");
    if (!m.sprgroup[0] && !m.sprgroup[1] &&
        !m.sprgroup[2] && m.sprgroup[3])     assert (m.sprcode == 3'd4) else $error("sprcode != 4 for group3");

    // pf front comparisons
    assert (m.pf1front == (m.sprcode > m.bplcon2[2:0])) else $error("pf1front mismatch");
    assert (m.pf2front == (m.sprcode > m.bplcon2[5:3])) else $error("pf2front mismatch");

    // sprsel logic equivalence (single concise check covers all branches/priority)
    logic exp_sprsel;
    exp_sprsel = (m.sprcode != 3'd7)
                 && !(m.pf1front && m.nplayfield[1])
                 && !(m.pf2front && m.nplayfield[2]);
    assert (m.sprsel == exp_sprsel) else $error("sprsel mismatch");

    // No X/Z on key outputs/internals
    assert (!$isunknown({m.sprsel, m.pf1front, m.pf2front, m.sprcode, m.sprgroup}))
      else $error("X/Z detected on internal/output signals");
  end

  // Functional coverage (immediate cover)
  always @* begin
    // sprcode choices
    cover (m.sprcode == 3'd7);
    cover (m.sprcode == 3'd1);
    cover (m.sprcode == 3'd2);
    cover (m.sprcode == 3'd3);
    cover (m.sprcode == 3'd4);

    // front comparisons toggle
    cover (m.pf1front);
    cover (!m.pf1front && (m.sprcode == m.bplcon2[2:0]));
    cover (m.pf2front);
    cover (!m.pf2front && (m.sprcode == m.bplcon2[5:3]));

    // sprsel outcomes and gating cases
    cover (m.sprsel == 1'b1);
    cover (m.sprsel == 1'b0);
    cover ((m.sprcode != 3'd7) && m.pf1front && m.nplayfield[1] && (m.sprsel == 1'b0));
    cover ((m.sprcode != 3'd7) && !m.pf1front && m.pf2front && m.nplayfield[2] && (m.sprsel == 1'b0));
    cover ((m.sprcode != 3'd7) && !(m.pf1front && m.nplayfield[1]) &&
           !(m.pf2front && m.nplayfield[2]) && (m.sprsel == 1'b1));
  end

endmodule

bind denise_spritepriority denise_spritepriority_sva sva_i();