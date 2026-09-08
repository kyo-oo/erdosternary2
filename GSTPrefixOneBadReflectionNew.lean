import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/--
Fresh prefix-one bad-reflection proof probe.

This theorem deliberately avoids the four-power creation master and the
master-based public prefix-one lift.  The contradiction is driven only by the
canonical seed-one bad language, a concrete child Happy gate, and the
kernel-checked Step-6 terminal packet.
-/
theorem gst_prefix_one_bad_reflection_new :
    GSTPrefixOneBadReflection := by
  intro s n hs hn
  dsimp only
  intro hParent j
  unfold GSTBadPair
  intro hChildHappy

  let T := gstNavigationConstant (s + 1) n
  let X := c s / 3 + 4^(3^s) * T

  have hChildNav : GSTNavigationWitness T := by
    rcases hChildHappy.2 with h0 | h3
    · exact gstNavigationWitness_of_digit_carry_zero T j hChildHappy.1 h0
    · exact gstNavigationWitness_of_digit_carry_three T j hChildHappy.1 h3

  have hOmegaBad : GSTOmegaInfiniteBadTrace s 1 n := by
    apply (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).2
    intro k
    have hk := hParent k
    simpa [GSTSeededAffineBadTrace, T, X, Nat.pow_one, c_mod3 s hs] using hk

  obtain ⟨q, hLeftHappy, hRightBad⟩ :=
    gst_step6_terminal_packet_kernel s n hs hn
      (by simpa [T] using hChildNav) hOmegaBad

  -- The Step-6 packet is the exact remaining collision seam: one left Happy
  -- cell against an all-depth bad right edge of the same canonical rectangle.
  -- Resolve that packet directly in the next compile/patch iterations.
  have hPacket :
      ∃ q,
        GSTU2DEventTransport.HappyCell
          (GSTGraphV2InfiniteControl.graph 1
            (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1))
            (s+2+q)).seven.carry
          (GSTGraphV2InfiniteControl.graph 1
            (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1))
            (s+2+q)).seven.digit ∧
        ∀ r, ¬ GSTU2DEventTransport.HappyCell
          (GSTGraphV2InfiniteControl.graph 1
            (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1) +
              GSTGraphV2PerfectPowerBlock.canonicalWidth s)
            (s+2+r)).seven.carry
          (GSTGraphV2InfiniteControl.graph 1
            (GSTGraphV2CanonicalNWave.nWaveShift s n (n+1) +
              GSTGraphV2PerfectPowerBlock.canonicalWidth s)
            (s+2+r)).seven.digit :=
    ⟨q, hLeftHappy, hRightBad⟩

  rcases hPacket with ⟨q, hLeftHappy, hRightBad⟩
  omega
