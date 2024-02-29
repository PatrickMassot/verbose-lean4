import Mathlib.Tactic
import Verbose.Tactics.Multilingual

import Verbose.Tactics.Extension

#suggestions_provider_sets

def provider : SuggestionProvider := fun _ _ ↦ pure ()
def providerbis : SuggestionProvider := fun _ _ ↦ pure ()
def providerter : SuggestionProvider := fun _ _ ↦ pure ()

SuggestionProviderSet test := provider providerbis

SuggestionProviderSet testt :=  test providerter

#suggestions_provider_sets

configureSuggestionProviders testt

#print_verbose_config
